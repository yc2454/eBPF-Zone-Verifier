CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra -Wpedantic -std=c11

BUILD_DIR := build

TOOL := $(BUILD_DIR)/canonical_hash_tool
SRCS := canonical_hash.c canonical_hash_tool.c
HDRS := canonical_hash.h siphash24.h

.PHONY: all clean
all: $(TOOL)

$(TOOL): $(SRCS) $(HDRS) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -o $@ $(SRCS)

$(BUILD_DIR):
	mkdir -p $@

clean:
	rm -rf $(BUILD_DIR)
