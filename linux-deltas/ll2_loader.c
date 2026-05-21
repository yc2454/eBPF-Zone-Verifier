// SPDX-License-Identifier: GPL-2.0-only
/*
 * ll2_loader.c — load a BPF program with a userspace-BCF bundle at
 * kernel verifier log_level 2 (state pruning / mark_precise / "N: safe"
 * / "from N to M" lines), and print the full log. Standalone; mirrors
 * the default (non-per-prog) path of test_loader.c.
 *
 * Usage: ll2_loader [--type TYPE] <prog.bpf.o> [<bundle.bcf-bundle>]
 */
#include "libbpf.h"
#include "bpf.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

static void *map_file(const char *path, size_t *sz)
{
	int fd = open(path, O_RDONLY);
	if (fd < 0) { perror("open bundle"); return NULL; }
	struct stat st;
	if (fstat(fd, &st)) { perror("fstat"); close(fd); return NULL; }
	void *p = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
	close(fd);
	if (p == MAP_FAILED) { perror("mmap"); return NULL; }
	*sz = st.st_size;
	return p;
}

int main(int argc, char **argv)
{
	const char *type_name = NULL, *prog_path = NULL, *bundle_path = NULL;
	const char *only_prog = NULL;
	int argi = 1;

	while (argi < argc &&
	       (strcmp(argv[argi], "--type") == 0 || strcmp(argv[argi], "--prog") == 0)) {
		if (strcmp(argv[argi], "--type") == 0)
			type_name = argv[argi + 1];
		else
			only_prog = argv[argi + 1];
		argi += 2;
	}
	if (argi >= argc) { fprintf(stderr, "need <prog.o>\n"); return 1; }
	prog_path = argv[argi++];
	if (argi < argc) bundle_path = argv[argi++];

	enum bpf_prog_type ptype = BPF_PROG_TYPE_UNSPEC;
	if (type_name && strcmp(type_name, "classifier") == 0)
		ptype = BPF_PROG_TYPE_SCHED_CLS;

	size_t bsz = 0;
	void *bundle = NULL;
	if (bundle_path) {
		bundle = map_file(bundle_path, &bsz);
		if (!bundle) return 1;
		printf("bundle: %s (%zu bytes)\n", bundle_path, bsz);
	}

	struct bpf_object *obj = bpf_object__open_file(prog_path, NULL);
	if (libbpf_get_error(obj)) {
		fprintf(stderr, "open %s failed\n", prog_path);
		return 1;
	}

	/* big per-program log buffer; log_level 2 = state + pruning */
	static const size_t LOGSZ = 64u << 20;
	char *logbuf = malloc(LOGSZ);
	logbuf[0] = '\0';

	struct bpf_program *prog;
	bpf_object__for_each_program(prog, obj) {
		if (only_prog) {
			int keep = strcmp(bpf_program__name(prog), only_prog) == 0;
			bpf_program__set_autoload(prog, keep);
			if (!keep)
				continue;
		}
		if (ptype != BPF_PROG_TYPE_UNSPEC)
			bpf_program__set_type(prog, ptype);
		if (bundle)
			bpf_program__set_bcf_bundle(prog, bundle, (unsigned)bsz);
		bpf_program__set_log_buf(prog, logbuf, LOGSZ);
		bpf_program__set_log_level(prog, 2);
	}

	int err = bpf_object__load(obj);
	/* dump the (single, shared) log buffer regardless of outcome */
	fputs(logbuf, stdout);
	printf("\n=== bpf_object__load err=%d (%s) ===\n",
	       err, err ? strerror(-err) : "OK");
	bpf_object__close(obj);
	if (bundle) munmap(bundle, bsz);
	return err ? 1 : 0;
}
