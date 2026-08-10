.DEFAULT_GOAL := all

CC      = gcc
CFLAGS  = -Wall -O2

VERSIONS = 1.43.0 1.44.2
TESTS    = test_3503_lifecycle test_combined

# libuv static lib name varies: libuv_a.a (cmake default) or libuv.a. The
# directory varies too — build_deps.sh pins CMAKE_INSTALL_LIBDIR to lib, but a
# tree built by other means lands in lib64 on RPM-based distributions, and this
# used to fail with a bare "no such file".
define find_libuv
$(firstword $(wildcard \
  deps/$(1)/lib/libuv_a.a deps/$(1)/lib/libuv.a \
  deps/$(1)/lib64/libuv_a.a deps/$(1)/lib64/libuv.a))
endef

define RULE
build/$(1)/$(2): src/$(2).c
	@mkdir -p $$(dir $$@)
	$$(CC) $$(CFLAGS) -o $$@ $$< \
		-I deps/$(1)/include \
		$$(call find_libuv,$(1)) \
		-lpthread -ldl -lrt
endef

$(foreach v,$(VERSIONS),$(foreach t,$(TESTS),$(eval $(call RULE,$(v),$(t)))))

ALL_TARGETS = $(foreach v,$(VERSIONS),$(foreach t,$(TESTS),build/$(v)/$(t)))

.PHONY: all clean

all: $(ALL_TARGETS)

clean:
	rm -rf build/
