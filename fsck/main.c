// SPDX-License-Identifier: GPL-2.0+
/*
 * Copyright 2021 Google LLC
 * Author: Daeho Jeong <daehojeong@google.com>
 * Contributor: Sergey Korkin <unix3dgforce@gmail.com>
 */

#define _GNU_SOURCE
#include <stdarg.h>
#include <stdlib.h>
#include <getopt.h>
#include <libgen.h>
#include <time.h>
#include <utime.h>
#include <unistd.h>
#include <sys/stat.h>
#include "erofs/print.h"
#include "erofs/io.h"
#include "erofs/compress.h"
#include "erofs/decompress.h"
#include "erofs/dir.h"
#include "erofs/xattr.h"
#include "erofs/hashtable.h"
#include "cJSON.h"

#define EA_HASHTABLE_BITS 16
#define VFS_CAP_FLAGS_EFFECTIVE 0x000001
#define VFS_CAP_REVISION_2 0x02000000
#define VFS_CAP_U32_1 1
#define VFS_CAP_REVISION_2 0x02000000
#define VFS_CAP_U32_2 2
#define VFS_CAP_U32 VFS_CAP_U32_2

static DECLARE_HASHTABLE(ea_hashtable, EA_HASHTABLE_BITS);
static LIST_HEAD(shared_xattrs_list);

cJSON *root = NULL;
cJSON *fs_config_array = NULL;
cJSON *symlinks_array = NULL;
cJSON *capabilities_array = NULL;

static unsigned int shared_xattrs_count, shared_xattrs_size;

static int erofsfsck_check_inode(erofs_nid_t pnid, erofs_nid_t nid);

struct xattr_item {
    const char *kvbuf;
    unsigned int hash[2], len[2], count;
    int shared_xattr_id;
    u8 prefix;
    struct hlist_node node;
};

struct inode_xattr_node {
    struct list_head list;
    struct xattr_item *item;
};

struct erofsfsck_cfg {
    u64 physical_blocks;
    u64 logical_blocks;
    char *extract_path;
    size_t extract_pos;
    mode_t umask;
    bool superuser;
    bool corrupted;
    bool print_comp_ratio;
    bool check_decomp;
    bool force;
    bool overwrite;
    bool preserve_owner;
    bool preserve_perms;
    bool save_fs_config;
    char *config_dir;
    char *config_file;
    size_t extract_path_base_pos;
};

static struct erofsfsck_cfg fsckcfg;

static struct option long_options[] = {
        {"help", no_argument, 0, 1},
        {"extract", optional_argument, 0, 2},
        {"save-config", optional_argument, 0, 3},
        {"device", required_argument, 0, 4},
        {"force", no_argument, 0, 5},
        {"overwrite", no_argument, 0, 6},
        {"preserve", no_argument, 0, 7},
        {"preserve-owner", no_argument, 0, 8},
        {"preserve-perms", no_argument, 0, 9},
        {"no-preserve", no_argument, 0, 10},
        {"no-preserve-owner", no_argument, 0, 11},
        {"no-preserve-perms", no_argument, 0, 12},
        {0, 0, 0, 0},
};

struct vfs_cap_data {
    __le32 magic_etc;
    struct {
        __le32 permitted;
        __le32 inheritable;
    } data[VFS_CAP_U32];
};

static inline char *__remove_extensions (char* file_path, char ext_sep, char path_sep) {
    char *result, *last_ext, *last_path;


    if (file_path == NULL) return NULL;
    if ((result = malloc (strlen (file_path) + 1)) == NULL) return NULL;

    strcpy (result, file_path);
    last_ext = strrchr (result, ext_sep);
    last_path = (path_sep == 0) ? NULL : strrchr (result, path_sep);

    if (last_ext != NULL) {
        if (last_path != NULL) {
            if (last_path < last_ext) {
                *last_ext = '\0';
            }
        } else {
            *last_ext = '\0';
        }
    }
    return result;
}

static inline int __create_dir(char *path_to_dir)
{
    if (mkdir(path_to_dir, 0700) < 0) {
        struct stat st;

        if (errno != EEXIST) {
            erofs_err("failed to create directory: %s (%s)",
                      path_to_dir, strerror(errno));
            return -errno;
        }

        if (lstat(path_to_dir, &st) ||
            !S_ISDIR(st.st_mode)) {
            erofs_err("path is not a directory: %s",
                      path_to_dir);
            return -ENOTDIR;
        }

        if (chmod(path_to_dir, 0700) < 0) {
            erofs_err("failed to set permissions: %s (%s)",
                      path_to_dir, strerror(errno));
            return -errno;
        }
    }
    return 0;
}

static inline int __write_to_config_file(char *file_path, char *data)
{
    FILE *fp;

    if((fp = fopen(file_path, "w")) == NULL)
    {
        erofs_err("Error occured while opening file: %s", file_path);
        return -EIO;
    }

    fprintf(fp, "%s\n", data);

    fclose(fp);
    return 0;
}

static inline int __save_config()
{
    erofs_info("Save config to: %s", fsckcfg.config_file);
    if (__write_to_config_file(fsckcfg.config_file, cJSON_Print(root)) < 0) return -EIO;

    return 0;
}

static inline int __init_json()
{
    root = cJSON_CreateObject();
    if (root == NULL) return -errno;

    fs_config_array = cJSON_CreateArray();
    if (fs_config_array == NULL) return -errno;

    symlinks_array = cJSON_CreateArray();
    if (symlinks_array == NULL) return -errno;

    capabilities_array = cJSON_CreateArray();
    if (capabilities_array == NULL) return -errno;

    cJSON_AddItemToObject(root, "Capabilities", capabilities_array);
    cJSON_AddItemToObject(root, "FSConfig", fs_config_array);
    cJSON_AddItemToObject(root, "Symlinks", symlinks_array);

    return 0;
}

static void __print_available_decompressors(FILE *f, const char *delim)
{
    unsigned int i = 0;
    const char *s;

    while ((s = z_erofs_list_available_compressors(i)) != NULL) {
        if (i++)
            fputs(delim, f);
        fputs(s, f);
    }
    fputc('\n', f);
}

static void __usage(void)
{
    fputs("usage: [options] IMAGE\n\n"
          "Check erofs filesystem compatibility and integrity of IMAGE, and [options] are:\n"
          " -V                     print the version number of fsck.erofs and exit\n"
          " -d#                    set output message level to # (maximum 9)\n"
          " -p                     print total compression ratio of all files\n"
          " --device=X             specify an extra device to be used together\n"
          " --extract[=X]          check if all files are well encoded, optionally extract to X\n"
          " --save-config=X        save fs_config & symlink file to directory X\n"
          " --help                 display this help and exit\n"
          "\nExtraction options (--extract=X is required):\n"
          " --force                allow extracting to root\n"
          " --overwrite            overwrite files that already exist\n"
          " --preserve             extract with the same ownership and permissions as on the filesystem\n"
          "                        (default for superuser)\n"
          " --preserve-owner       extract with the same ownership as on the filesystem\n"
          " --preserve-perms       extract with the same permissions as on the filesystem\n"
          " --no-preserve          extract as yourself and apply user's umask on permissions\n"
          "                        (default for ordinary users)\n"
          " --no-preserve-owner    extract as yourself\n"
          " --no-preserve-perms    apply user's umask when extracting permissions\n"
          "\nSupported algorithms are: ", stderr);
    __print_available_decompressors(stderr, ", ");
}

static unsigned int BKDRHash(char *str, unsigned int len)
{
    const unsigned int seed = 131313;
    unsigned int hash = 0;

    while (len) {
        hash = hash * seed + (*str++);
        --len;
    }
    return hash;
}

static unsigned int xattr_item_hash(u8 prefix, char *buf, unsigned int len[2], unsigned int hash[2])
{
    hash[0] = BKDRHash(buf, len[0]);	/* key */
    hash[1] = BKDRHash(buf + len[0], len[1]);	/* value */

    return prefix ^ hash[0] ^ hash[1];
}

static int inode_xattr_add(struct list_head *hlist, struct xattr_item *item)
{
    struct inode_xattr_node *node = malloc(sizeof(*node));

    if (!node)
        return -ENOMEM;
    init_list_head(&node->list);
    node->item = item;
    list_add(&node->list, hlist);
    return 0;
}

static int shared_xattr_add(struct xattr_item *item)
{
    struct inode_xattr_node *node = malloc(sizeof(*node));

    if (!node)
        return -ENOMEM;

    init_list_head(&node->list);
    node->item = item;
    list_add(&node->list, &shared_xattrs_list);

    shared_xattrs_size += sizeof(struct erofs_xattr_entry);
    shared_xattrs_size = EROFS_XATTR_ALIGN(shared_xattrs_size +
                                           item->len[0] + item->len[1]);
    return ++shared_xattrs_count;
}

static struct xattr_item *get_xattritem(u8 prefix, char *kvbuf, unsigned int len[2])
{
    struct xattr_item *item;
    unsigned int hash[2], hkey;

    hkey = xattr_item_hash(prefix, kvbuf, len, hash);

    hash_for_each_possible(ea_hashtable, item, node, hkey) {
        if (prefix == item->prefix &&
            item->len[0] == len[0] && item->len[1] == len[1] &&
            item->hash[0] == hash[0] && item->hash[1] == hash[1] &&
            !memcmp(kvbuf, item->kvbuf, len[0] + len[1])) {
            free(kvbuf);
            ++item->count;
            return item;
        }
    }

    item = malloc(sizeof(*item));
    if (!item) {
        free(kvbuf);
        return ERR_PTR(-ENOMEM);
    }
    INIT_HLIST_NODE(&item->node);
    item->count = 1;
    item->kvbuf = kvbuf;
    item->len[0] = len[0];
    item->len[1] = len[1];
    item->hash[0] = hash[0];
    item->hash[1] = hash[1];
    item->shared_xattr_id = -1;
    item->prefix = prefix;
    hash_add(ea_hashtable, &item->node, hkey);
    return item;
}

static void erofsfsck_print_version(void)
{
    fprintf(stderr, "fsck.erofs %s\n", cfg.c_version);
}

static int erofsfsck_parse_options_cfg(int argc, char **argv)
{
    int opt, ret;
    bool has_opt_preserve = false;

    while ((opt = getopt_long(argc, argv, "Vd:p",
                              long_options, NULL)) != -1) {
        switch (opt) {
            case 'V':
                erofsfsck_print_version();
                exit(0);
            case 'd':
                ret = atoi(optarg);
                if (ret < EROFS_MSG_MIN || ret > EROFS_MSG_MAX) {
                    erofs_err("invalid debug level %d", ret);
                    return -EINVAL;
                }
                cfg.c_dbg_lvl = ret;
                break;
            case 'p':
                fsckcfg.print_comp_ratio = true;
                break;
            case 1:
                __usage();
                exit(0);
            case 2:
                fsckcfg.check_decomp = true;
                if (optarg) {
                    size_t len = strlen(optarg);

                    if (len == 0) {
                        erofs_err("empty value given for --extract=X");
                        return -EINVAL;
                    }

                    /* remove trailing slashes except root */
                    while (len > 1 && optarg[len - 1] == '/')
                        len--;

                    fsckcfg.extract_path = malloc(PATH_MAX);
                    if (!fsckcfg.extract_path)
                        return -ENOMEM;
                    strncpy(fsckcfg.extract_path, optarg, len);
                    fsckcfg.extract_path[len] = '\0';
                    /* if path is root, start writing from position 0 */
                    if (len == 1 && fsckcfg.extract_path[0] == '/')
                        len = 0;
                    fsckcfg.extract_pos = len;
                    fsckcfg.extract_path_base_pos = len;
                }
                break;
            case 3:
                fsckcfg.save_fs_config = true;
                if (optarg) {
                    size_t len = strlen(optarg);

                    if (len == 0) {
                        erofs_err("empty value given for --save-config-dir=X");
                        return -EINVAL;
                    }

                    fsckcfg.config_dir = malloc(PATH_MAX);

                    if (!fsckcfg.config_dir)
                        return -ENOMEM;

                    while (len > 1 && optarg[len - 1] == '/')
                        len--;

                    if (asprintf(&fsckcfg.config_dir, "%s/config", optarg) < 0)
                        return -ENOMEM;

                    ret = __create_dir(fsckcfg.config_dir);
                    if (ret)
                        return -errno;
                }
                break;
            case 4:
                ret = blob_open_ro(optarg);
                if (ret)
                    return ret;
                ++sbi.extra_devices;
                break;
            case 5:
                fsckcfg.force = true;
                break;
            case 6:
                fsckcfg.overwrite = true;
                break;
            case 7:
                fsckcfg.preserve_owner = fsckcfg.preserve_perms = true;
                has_opt_preserve = true;
                break;
            case 8:
                fsckcfg.preserve_owner = true;
                has_opt_preserve = true;
                break;
            case 9:
                fsckcfg.preserve_perms = true;
                has_opt_preserve = true;
                break;
            case 10:
                fsckcfg.preserve_owner = fsckcfg.preserve_perms = false;
                has_opt_preserve = true;
                break;
            case 11:
                fsckcfg.preserve_owner = false;
                has_opt_preserve = true;
                break;
            case 12:
                fsckcfg.preserve_perms = false;
                has_opt_preserve = true;
                break;
            default:
                return -EINVAL;
        }
    }

    if (fsckcfg.extract_path) {
        if (!fsckcfg.extract_pos && !fsckcfg.force) {
            erofs_err("--extract=/ must be used together with --force");
            return -EINVAL;
        }
    } else {
        if (fsckcfg.force) {
            erofs_err("--force must be used together with --extract=X");
            return -EINVAL;
        }
        if (fsckcfg.overwrite) {
            erofs_err("--overwrite must be used together with --extract=X");
            return -EINVAL;
        }
        if (has_opt_preserve) {
            erofs_err("--[no-]preserve[-owner/-perms] must be used together with --extract=X");
            return -EINVAL;
        }
    }

    if (optind >= argc) {
        erofs_err("missing argument: IMAGE");
        return -EINVAL;
    }

    cfg.c_img_path = strdup(argv[optind++]);
    if (!cfg.c_img_path)
        return -ENOMEM;

    if (fsckcfg.save_fs_config) {
        //TODO Подвергнуть рефакторингу
        char *filename;

        fsckcfg.config_file = malloc(PATH_MAX);

        filename = __remove_extensions(basename(strdup(cfg.c_img_path)), '.', '/');

        if (!fsckcfg.config_file)
            return -ENOMEM;

        if (asprintf(&fsckcfg.config_file, "%s/%s_config.json", fsckcfg.config_dir, filename) < 0)
            return -ENOMEM;

        free(filename);
    }

    if (optind < argc) {
        erofs_err("unexpected argument: %s", argv[optind]);
        return -EINVAL;
    }
    return 0;
}

static void erofsfsck_set_attributes(struct erofs_inode *inode, char *path)
{
    int ret;

    /* don't apply attributes when fsck is used without extraction */
    if (!fsckcfg.extract_path)
        return;

#ifdef HAVE_UTIMENSAT
    if (utimensat(AT_FDCWD, path, (struct timespec []) {
				[0] = { .tv_sec = inode->i_mtime,
					.tv_nsec = inode->i_mtime_nsec },
				[1] = { .tv_sec = inode->i_mtime,
					.tv_nsec = inode->i_mtime_nsec },
			}, AT_SYMLINK_NOFOLLOW) < 0)
#else
    if (utime(path, &((struct utimbuf){.actime = inode->i_mtime,
            .modtime = inode->i_mtime})) < 0)
#endif
        erofs_warn("failed to set times: %s", path);

    if (!S_ISLNK(inode->i_mode)) {
        if (fsckcfg.preserve_perms)
            ret = chmod(path, inode->i_mode);
        else
            ret = chmod(path, inode->i_mode & ~fsckcfg.umask);
        if (ret < 0)
            erofs_warn("failed to set permissions: %s", path);
    }

    if (fsckcfg.preserve_owner) {
        ret = lchown(path, inode->i_uid, inode->i_gid);
        if (ret < 0)
            erofs_warn("failed to change ownership: %s", path);
    }
}

static int erofsfsck_dirent_iter(struct erofs_dir_context *ctx)
{
    int ret;
    size_t prev_pos = fsckcfg.extract_pos;

    if (ctx->dot_dotdot)
        return 0;

    if (fsckcfg.extract_path) {
        size_t curr_pos = prev_pos;

        fsckcfg.extract_path[curr_pos++] = '/';
        strncpy(fsckcfg.extract_path + curr_pos, ctx->dname,
                ctx->de_namelen);
        curr_pos += ctx->de_namelen;
        fsckcfg.extract_path[curr_pos] = '\0';
        fsckcfg.extract_pos = curr_pos;
    }

    ret = erofsfsck_check_inode(ctx->dir->nid, ctx->de_nid);

    if (fsckcfg.extract_path) {
        fsckcfg.extract_path[prev_pos] = '\0';
        fsckcfg.extract_pos = prev_pos;
    }
    return ret;
}

static int erofs_check_sb_chksum(void)
{
    int ret;
    u8 buf[EROFS_BLKSIZ];
    u32 crc;
    struct erofs_super_block *sb;

    ret = blk_read(0, buf, 0, 1);
    if (ret) {
        erofs_err("failed to read superblock to check checksum: %d",
                  ret);
        return -1;
    }

    sb = (struct erofs_super_block *)(buf + EROFS_SUPER_OFFSET);
    sb->checksum = 0;

    crc = erofs_crc32c(~0, (u8 *)sb, EROFS_BLKSIZ - EROFS_SUPER_OFFSET);
    if (crc != sbi.checksum) {
        erofs_err("superblock chksum doesn't match: saved(%08xh) calculated(%08xh)",
                  sbi.checksum, crc);
        fsckcfg.corrupted = true;
        return -1;
    }
    return 0;
}

static int erofs_xattr_add(struct list_head *ixattrs, struct xattr_item *item)
{
    if (ixattrs)
        return inode_xattr_add(ixattrs, item);

    if (item->count == cfg.c_inline_xattr_tolerance + 1) {
        int ret = shared_xattr_add(item);

        if (ret < 0)
            return ret;
    }
    return 0;
}

static struct xattr_item *erofs_get_selabel_xattr(struct erofs_xattr_entry *entry, erofs_off_t addr)
{
    int ret = 0;
    struct xattr_item *item;
    unsigned int len[2];
    char *kvbuf;

    len[0] = entry->e_name_len;
    len[1] = entry->e_value_size;

    kvbuf = malloc(len[0] + len[1] + 1);
    if (!kvbuf) {
        free(kvbuf);
        return ERR_PTR(-ENOMEM);
    }

    ret = dev_read(0, kvbuf, addr, len[0] + len[1]);
    if (ret){
        free(kvbuf);
        return ERR_PTR(-errno);
    }

    kvbuf[len[0] + len[1]] = '\0';

    item = get_xattritem(EROFS_XATTR_INDEX_SECURITY, kvbuf, len);
    if (IS_ERR(item)){
        free(kvbuf);
        return ERR_PTR(-errno);
    }

    return item;
}

static struct xattr_item *erofs_get_caps_xattr(struct erofs_xattr_entry *entry, erofs_off_t addr)
{
    int ret = 0;
    struct xattr_item *item;
    unsigned int len[2];
//    struct vfs_cap_data *caps;
    char *capbuf;
    char *kvbuf;

    len[0] = entry->e_name_len;
    len[1] = entry->e_value_size;

    capbuf = malloc(len[1]);
    if (!capbuf) {
        free(capbuf);
        return ERR_PTR(-ENOMEM);
    }

    kvbuf = malloc(len[0] + len[1]);
    if (!kvbuf) {
        free(kvbuf);
        return ERR_PTR(-ENOMEM);
    }

    ret = dev_read(0, capbuf, addr + len[0], len[1]);
    if (ret) {
        free(kvbuf);
        return ERR_PTR(-errno);
    }

//    caps = (struct vfs_cap_data *)capbuf;
    memcpy(kvbuf, "capability", len[0]);
    memcpy(kvbuf + len[0], capbuf, len[1]);

    item = get_xattritem(EROFS_XATTR_INDEX_SECURITY, kvbuf, len);
    if (IS_ERR(item)){
        free(kvbuf);
        return ERR_PTR(-errno);
    }

    return item;
}

static int erofs_verify_xattr(struct erofs_inode *inode)
{
    unsigned int xattr_hdr_size = sizeof(struct erofs_xattr_ibody_header);
    unsigned int xattr_entry_size = sizeof(struct erofs_xattr_entry);
    erofs_off_t addr;
    unsigned int ofs, xattr_shared_count;
    struct erofs_xattr_ibody_header *ih;
    struct erofs_xattr_entry *entry;
    int i, remaining = inode->xattr_isize, ret = 0;
    char buf[EROFS_BLKSIZ];
    struct xattr_item *item;

    init_list_head(&inode->i_xattrs);

    if (inode->xattr_isize == xattr_hdr_size) {
        erofs_err("xattr_isize %d of nid %llu is not supported yet",
                  inode->xattr_isize, inode->nid | 0ULL);
        ret = -EFSCORRUPTED;
        goto out;
    } else if (inode->xattr_isize < xattr_hdr_size) {
        if (inode->xattr_isize) {
            erofs_err("bogus xattr ibody @ nid %llu",
                      inode->nid | 0ULL);
            ret = -EFSCORRUPTED;
            goto out;
        }
    }

    addr = iloc(inode->nid) + inode->inode_isize;
    ret = dev_read(0, buf, addr, xattr_hdr_size);
    if (ret < 0) {
        erofs_err("failed to read xattr header @ nid %llu: %d",
                  inode->nid | 0ULL, ret);
        goto out;
    }
    ih = (struct erofs_xattr_ibody_header *)buf;
    xattr_shared_count = ih->h_shared_count;

    ofs = erofs_blkoff(addr) + xattr_hdr_size;
    addr += xattr_hdr_size;
    remaining -= xattr_hdr_size;
    for (i = 0; i < xattr_shared_count; ++i) {
        if (ofs >= EROFS_BLKSIZ) {
            if (ofs != EROFS_BLKSIZ) {
                erofs_err("unaligned xattr entry in xattr shared area @ nid %llu",
                          inode->nid | 0ULL);
                ret = -EFSCORRUPTED;
                goto out;
            }
            ofs = 0;
        }
        ofs += xattr_entry_size;
        addr += xattr_entry_size;
        remaining -= xattr_entry_size;
    }

    while (remaining > 0) {
        unsigned int entry_sz;

        ret = dev_read(0, buf, addr, xattr_entry_size);
        if (ret) {
            erofs_err("failed to read xattr entry @ nid %llu: %d",
                      inode->nid | 0ULL, ret);
            goto out;
        }

        entry = (struct erofs_xattr_entry *)buf;

        char *name = malloc(entry->e_name_len + 1);

        ret = dev_read(0, name, addr + xattr_entry_size, entry->e_name_len);
        if (ret) {
            erofs_err("failed to read xattr entry @ nid %llu: %d",
                      inode->nid | 0ULL, ret);
            goto out;
        }

        name[entry->e_name_len] = '\0';

        if (strcmp(name, "selinux")==0){
            item = erofs_get_selabel_xattr(entry, addr + xattr_entry_size);

            if (IS_ERR(item)) {
                erofs_err("failed to read xattr entry @ nid %llu: %d",
                          inode->nid | 0ULL, ret);
                ret = PTR_ERR(item);
                goto out;
            }

            if (item)
            {
                ret = erofs_xattr_add(&inode->i_xattrs, item);
                if(ret)
                    goto out;
            }
        } else if (strcmp(name, "capability")==0)
        {
            item = erofs_get_caps_xattr(entry, addr + xattr_entry_size);

            if (IS_ERR(item)) {
                erofs_err("failed to read xattr entry @ nid %llu: %d",
                          inode->nid | 0ULL, ret);
                ret = PTR_ERR(item);
                goto out;
            }

            if (item)
            {
                ret = erofs_xattr_add(&inode->i_xattrs, item);
                if(ret)
                    goto out;
            }
        }

        entry_sz = erofs_xattr_entry_size(entry);
        if (remaining < entry_sz) {
            erofs_err("xattr on-disk corruption: xattr entry beyond xattr_isize @ nid %llu",
                      inode->nid | 0ULL);
            ret = -EFSCORRUPTED;
            goto out;
        }
        addr += entry_sz;
        remaining -= entry_sz;
    }
    out:
    return ret;
}

static int erofs_verify_inode_data(struct erofs_inode *inode, int outfd)
{
    struct erofs_map_blocks map = {
            .index = UINT_MAX,
    };
    struct erofs_map_dev mdev;
    int ret = 0;
    bool compressed;
    erofs_off_t pos = 0;
    u64 pchunk_len = 0;
    unsigned int raw_size = 0, buffer_size = 0;
    char *raw = NULL, *buffer = NULL;

    erofs_dbg("verify data chunk of nid(%llu): type(%d)",
              inode->nid | 0ULL, inode->datalayout);

    switch (inode->datalayout) {
        case EROFS_INODE_FLAT_PLAIN:
        case EROFS_INODE_FLAT_INLINE:
        case EROFS_INODE_CHUNK_BASED:
            compressed = false;
            break;
        case EROFS_INODE_FLAT_COMPRESSION_LEGACY:
        case EROFS_INODE_FLAT_COMPRESSION:
            compressed = true;
            break;
        default:
            erofs_err("unknown datalayout");
            return -EINVAL;
    }

    while (pos < inode->i_size) {
        map.m_la = pos;
        if (compressed)
            ret = z_erofs_map_blocks_iter(inode, &map,
                                          EROFS_GET_BLOCKS_FIEMAP);
        else
            ret = erofs_map_blocks(inode, &map,
                                   EROFS_GET_BLOCKS_FIEMAP);
        if (ret)
            goto out;

        if (!compressed && map.m_llen != map.m_plen) {
            erofs_err("broken chunk length m_la %" PRIu64 " m_llen %" PRIu64 " m_plen %" PRIu64,
                    map.m_la, map.m_llen, map.m_plen);
            ret = -EFSCORRUPTED;
            goto out;
        }

        /* the last lcluster can be divided into 3 parts */
        if (map.m_la + map.m_llen > inode->i_size)
            map.m_llen = inode->i_size - map.m_la;

        pchunk_len += map.m_plen;
        pos += map.m_llen;

        /* should skip decomp? */
        if (!(map.m_flags & EROFS_MAP_MAPPED) || !fsckcfg.check_decomp)
            continue;

        if (map.m_plen > raw_size) {
            raw_size = map.m_plen;
            raw = realloc(raw, raw_size);
            BUG_ON(!raw);
        }

        mdev = (struct erofs_map_dev) {
                .m_deviceid = map.m_deviceid,
                .m_pa = map.m_pa,
        };
        ret = erofs_map_dev(&sbi, &mdev);
        if (ret) {
            erofs_err("failed to map device of m_pa %" PRIu64 ", m_deviceid %u @ nid %llu: %d",
                    map.m_pa, map.m_deviceid, inode->nid | 0ULL,
                    ret);
            goto out;
        }

        if (compressed && map.m_llen > buffer_size) {
            buffer_size = map.m_llen;
            buffer = realloc(buffer, buffer_size);
            BUG_ON(!buffer);
        }

        ret = dev_read(mdev.m_deviceid, raw, mdev.m_pa, map.m_plen);
        if (ret < 0) {
            erofs_err("failed to read data of m_pa %" PRIu64 ", m_plen %" PRIu64 " @ nid %llu: %d",
                    mdev.m_pa, map.m_plen, inode->nid | 0ULL,
                    ret);
            goto out;
        }

        if (compressed) {
            struct z_erofs_decompress_req rq = {
                    .in = raw,
                    .out = buffer,
                    .decodedskip = 0,
                    .inputsize = map.m_plen,
                    .decodedlength = map.m_llen,
                    .alg = map.m_algorithmformat,
                    .partial_decoding = 0
            };

            ret = z_erofs_decompress(&rq);
            if (ret < 0) {
                erofs_err("failed to decompress data of m_pa %" PRIu64 ", m_plen %" PRIu64 " @ nid %llu: %s",
                        mdev.m_pa, map.m_plen,
                        inode->nid | 0ULL, strerror(-ret));
                goto out;
            }
        }

        if (outfd >= 0 && write(outfd, compressed ? buffer : raw,
                                map.m_llen) < 0) {
            erofs_err("I/O error occurred when verifying data chunk @ nid %llu",
                      inode->nid | 0ULL);
            ret = -EIO;
            goto out;
        }
    }

    if (fsckcfg.print_comp_ratio) {
        fsckcfg.logical_blocks +=
                DIV_ROUND_UP(inode->i_size, EROFS_BLKSIZ);
        fsckcfg.physical_blocks +=
                DIV_ROUND_UP(pchunk_len, EROFS_BLKSIZ);
    }
    out:
    if (raw)
        free(raw);
    if (buffer)
        free(buffer);
    return ret < 0 ? ret : 0;
}

static inline int erofs_extract_dir(struct erofs_inode *inode)
{
    int ret;

    erofs_dbg("create directory %s", fsckcfg.extract_path);

    /* verify data chunk layout */
    ret = erofs_verify_inode_data(inode, -1);
    if (ret)
        return ret;

    if (fsckcfg.save_fs_config){
        char *buf = (char *)malloc(6 * sizeof(char));

        size_t len = strlen(fsckcfg.extract_path) - fsckcfg.extract_path_base_pos + 1;
        char *truncated_path = (char *)malloc(len * sizeof(char));
        strncpy(truncated_path, fsckcfg.extract_path + fsckcfg.extract_path_base_pos, len);

        if (truncated_path[0] == '\0')
        {
            truncated_path[0] = '/';
        }

        cJSON *dir_item = cJSON_CreateObject();
        cJSON *dir_permission = cJSON_CreateObject();
        cJSON_AddItemToArray(fs_config_array, dir_item);
        cJSON_AddItemToObject(dir_item, "target", cJSON_CreateString(truncated_path));
        cJSON_AddItemToObject(dir_item, "directory", dir_permission);
        cJSON_AddItemToObject(dir_permission, "uid", cJSON_CreateNumber(inode->i_uid));
        cJSON_AddItemToObject(dir_permission, "gid", cJSON_CreateNumber(inode->i_gid));
        sprintf(buf, "%#o", inode->i_mode & 0x0FFF);
        cJSON_AddItemToObject(dir_permission, "permission", cJSON_CreateString(buf));

        free(truncated_path);
    }

    /*
     * Make directory with default user rwx permissions rather than
     * the permissions from the filesystem, as these may not have
     * write/execute permission.  These are fixed up later in
     * erofsfsck_set_attributes().
     */
    ret = __create_dir(fsckcfg.extract_path);
    if (ret)
        return ret;

    return 0;
}

static uint64_t erofs_get_capabilities(struct list_head *ixattrs){
    struct inode_xattr_node *node;
    uint64_t result = 0;
    char caps_str[16];

    list_for_each_entry(node, ixattrs, list) {
        const struct xattr_item *item = node->item;

        char *name = malloc(item->len[0] + 1);
        strncpy(name, item->kvbuf, item->len[0]);
        name[item->len[0]] = '\0';

        if (strcmp(name, "capability")==0){
            struct vfs_cap_data *caps;
            char *caps_buf = malloc(item->len[1]);

            memcpy(caps_buf, item->kvbuf + item->len[0], item->len[1]);
            caps = (struct vfs_cap_data *)caps_buf;
            erofs_dbg("magic: %x DATA[0]: %04x DATA[1]: %04x  DATA[2]: %04x DATA[3]: %04x", caps->magic_etc, caps->data[1].permitted, caps->data[1].inheritable, caps->data[0].permitted, caps->data[0].inheritable);

            sprintf(caps_str,"%04x%04x%04x", caps->data[1].permitted, caps->data[1].inheritable, caps->data[0].permitted);
            result = strtoull(caps_str, NULL, 16);
        }
    }
    return result;
}

static inline int erofs_extract_file(struct erofs_inode *inode)
{
    bool tryagain = true;
    int ret, fd;
    struct list_head *ixattrs = &inode->i_xattrs;
    uint64_t capabilities;

    erofs_dbg("extract file to path: %s", fsckcfg.extract_path);

    again:
    fd = open(fsckcfg.extract_path,
              O_WRONLY | O_CREAT | O_NOFOLLOW |
              (fsckcfg.overwrite ? O_TRUNC : O_EXCL), 0700);
    if (fd < 0) {
        if (fsckcfg.overwrite && tryagain) {
            if (errno == EISDIR) {
                erofs_warn("try to forcely remove directory %s",
                           fsckcfg.extract_path);
                if (rmdir(fsckcfg.extract_path) < 0) {
                    erofs_err("failed to remove: %s (%s)",
                              fsckcfg.extract_path, strerror(errno));
                    return -EISDIR;
                }
            } else if (errno == EACCES &&
                       chmod(fsckcfg.extract_path, 0700) < 0) {
                erofs_err("failed to set permissions: %s (%s)",
                          fsckcfg.extract_path, strerror(errno));
                return -errno;
            }
            tryagain = false;
            goto again;
        }
        erofs_err("failed to open: %s (%s)", fsckcfg.extract_path,
                  strerror(errno));
        return -errno;
    }

    /* verify data chunk layout */
    ret = erofs_verify_inode_data(inode, fd);
    if (ret)
        return ret;

    if (fsckcfg.save_fs_config){

        char *buf = (char *)malloc(6 * sizeof(char));

        size_t len = strlen(fsckcfg.extract_path) - fsckcfg.extract_path_base_pos + 1;
        char *truncated_path = (char *)malloc(len * sizeof(char));
        strncpy(truncated_path, fsckcfg.extract_path + fsckcfg.extract_path_base_pos, len);

        capabilities = erofs_get_capabilities(ixattrs);

        cJSON *file_item = cJSON_CreateObject();
        cJSON *file_permission = cJSON_CreateObject();
        cJSON_AddItemToArray(fs_config_array, file_item);
        cJSON_AddItemToObject(file_item, "target", cJSON_CreateString(truncated_path));
        cJSON_AddItemToObject(file_item, "file", file_permission);
        cJSON_AddItemToObject(file_permission, "uid", cJSON_CreateNumber(inode->i_uid));
        cJSON_AddItemToObject(file_permission, "gid", cJSON_CreateNumber(inode->i_gid));
        sprintf(buf, "%#o", inode->i_mode & 0x0FFF);
        cJSON_AddItemToObject(file_permission, "permission", cJSON_CreateString(buf));
        if (capabilities > 0)
        {
            char *caps = NULL;
            asprintf(&caps, "0x%lx", capabilities);
            cJSON_AddItemToObject(file_permission, "capabilities", cJSON_CreateString(caps));
        }

        free(truncated_path);
    }

    if (close(fd))
        return -errno;
    return ret;
}

static inline int erofs_extract_symlink(struct erofs_inode *inode)
{
    bool tryagain = true;
    int ret;
    char *buf = NULL;
    char *target = NULL;
    char *source = NULL;

    erofs_dbg("extract symlink to path: %s", fsckcfg.extract_path);

    /* verify data chunk layout */
    ret = erofs_verify_inode_data(inode, -1);
    if (ret)
        return ret;

    buf = malloc(inode->i_size + 1);
    if (!buf) {
        ret = -ENOMEM;
        goto out;
    }

    ret = erofs_pread(inode, buf, inode->i_size, 0);
    if (ret) {
        erofs_err("I/O error occurred when reading symlink @ nid %llu: %d",
                  inode->nid | 0ULL, ret);
        goto out;
    }

    buf[inode->i_size] = '\0';
    again:
    if (fsckcfg.save_fs_config){
        target =  malloc(inode->i_size + 1);
        if (!target){
            ret = -ENOMEM;
            goto out;
        }

        size_t len = strlen(fsckcfg.extract_path) - fsckcfg.extract_path_base_pos + 1;
        source = (char *)malloc(len * sizeof(char));
        if (!source){
            ret = -ENOMEM;
            goto out;
        }

        strcpy(target, buf);
        strncpy(source, fsckcfg.extract_path + fsckcfg.extract_path_base_pos, len);

        cJSON *symlink = cJSON_CreateObject();
        cJSON_AddItemToArray(symlinks_array, symlink);
        cJSON_AddItemToObject(symlink, "target", cJSON_CreateString(target));
        cJSON_AddItemToObject(symlink, "source", cJSON_CreateString(source));
    }

    if (symlink(buf, fsckcfg.extract_path) < 0) {
        if (errno == EEXIST && fsckcfg.overwrite && tryagain) {
            erofs_warn("try to forcely remove file %s",
                       fsckcfg.extract_path);
            if (unlink(fsckcfg.extract_path) < 0) {
                erofs_err("failed to remove: %s",
                          fsckcfg.extract_path);
                ret = -errno;
                goto out;
            }
            tryagain = false;
            goto again;
        }
        erofs_err("failed to create symlink: %s",
                  fsckcfg.extract_path);
        ret = -errno;
    }
    out:
    if (buf)
        free(buf);

    if (target)
        free(target);

    if (source)
        free(source);

    return ret;
}

static int erofsfsck_check_inode(erofs_nid_t pnid, erofs_nid_t nid)
{
    int ret;
    struct erofs_inode inode;

    erofs_dbg("check inode: nid(%llu)", nid | 0ULL);

    inode.nid = nid;
    ret = erofs_read_inode_from_disk(&inode);
    if (ret) {
        if (ret == -EIO)
            erofs_err("I/O error occurred when reading nid(%llu)",
                      nid | 0ULL);
        goto out;
    }

    /* verify xattr field */
    ret = erofs_verify_xattr(&inode);
    if (ret)
        goto out;

    if (fsckcfg.extract_path) {
        switch (inode.i_mode & S_IFMT) {
            case S_IFDIR:
                ret = erofs_extract_dir(&inode);
                break;
            case S_IFREG:
                ret = erofs_extract_file(&inode);
                break;
            case S_IFLNK:
                ret = erofs_extract_symlink(&inode);
                break;
            default:
                /* TODO */
                goto verify;
        }
    } else {
        verify:
        /* verify data chunk layout */
        ret = erofs_verify_inode_data(&inode, -1);
    }
    if (ret)
        goto out;

    /* XXXX: the dir depth should be restricted in order to avoid loops */
    if (S_ISDIR(inode.i_mode)) {
        struct erofs_dir_context ctx = {
                .flags = EROFS_READDIR_VALID_PNID,
                .pnid = pnid,
                .dir = &inode,
                .cb = erofsfsck_dirent_iter,
        };

        ret = erofs_iterate_dir(&ctx, true);
    }

    if (!ret)
        erofsfsck_set_attributes(&inode, fsckcfg.extract_path);

    out:
    if (ret && ret != -EIO)
        fsckcfg.corrupted = true;
    return ret;
}

int main(int argc, char **argv)
{
    int err;

    clock_t tic = clock();

    erofs_init_configure();

    err = __init_json();
    if(err < 0)
    {
        erofs_err("JSON initialization error");
        goto exit;
    }

    fsckcfg.physical_blocks = 0;
    fsckcfg.logical_blocks = 0;
    fsckcfg.extract_path = NULL;
    fsckcfg.extract_pos = 0;
    fsckcfg.umask = umask(0);
    fsckcfg.superuser = geteuid() == 0;
    fsckcfg.corrupted = false;
    fsckcfg.print_comp_ratio = false;
    fsckcfg.check_decomp = false;
    fsckcfg.force = false;
    fsckcfg.overwrite = false;
    fsckcfg.preserve_owner = fsckcfg.superuser;
    fsckcfg.preserve_perms = fsckcfg.superuser;
    fsckcfg.save_fs_config = false;
    fsckcfg.config_dir = NULL;
    fsckcfg.extract_path_base_pos = 0;
    fsckcfg.config_file = NULL;

    err = erofsfsck_parse_options_cfg(argc, argv);
    if (err) {
        if (err == -EINVAL)
            __usage();
        goto exit;
    }

    err = dev_open_ro(cfg.c_img_path);
    if (err) {
        erofs_err("failed to open image file");
        goto exit;
    }

    err = erofs_read_superblock();
    if (err) {
        erofs_err("failed to read superblock");
        goto exit_dev_close;
    }

    if (erofs_sb_has_sb_chksum() && erofs_check_sb_chksum()) {
        erofs_err("failed to verify superblock checksum");
        goto exit_dev_close;
    }

    err = erofsfsck_check_inode(sbi.root_nid, sbi.root_nid);
    if (fsckcfg.corrupted) {
        if (!fsckcfg.extract_path)
            erofs_err("Found some filesystem corruption");
        else
            erofs_err("Failed to extract filesystem");
        err = -EFSCORRUPTED;
    } else if (!err) {
        if (!fsckcfg.extract_path)
            erofs_info("No errors found");
        else
            erofs_info("Extracted filesystem successfully");

        if (fsckcfg.print_comp_ratio) {
            double comp_ratio =
                    (double)fsckcfg.physical_blocks * 100 /
                    (double)fsckcfg.logical_blocks;

            erofs_info("Compression ratio: %.2f(%%)", comp_ratio);
        }
    }

    if (fsckcfg.save_fs_config)
    {
        __save_config();
    }
    exit_dev_close:
    dev_close();
    exit:
    blob_closeall();
    erofs_exit_configure();
    clock_t toc = clock();
    erofs_info("Elapsed: %f seconds\n", (double)(toc - tic) / CLOCKS_PER_SEC);
    return err ? 1 : 0;
}
