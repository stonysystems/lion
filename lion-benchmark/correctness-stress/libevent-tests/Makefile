.DEFAULT_GOAL := all

CC      = gcc
CFLAGS  = -Wall -O2 -Wno-deprecated-declarations

VERSIONS = 2.1.5-beta 2.1.11-stable 2.1.12-stable
TESTS_CORE = test_237_filter test_984_phantom test_combined
TESTS_SSL  = test_232_ssl

# Core tests: link libevent only
define CORE_RULE
build/$(1)/$(2): src/$(2).c
	@mkdir -p $$(dir $$@)
	$$(CC) $$(CFLAGS) -o $$@ $$< \
		-I deps/$(1)/include \
		deps/$(1)/lib/libevent.a \
		deps/$(1)/lib/libevent_core.a \
		-lpthread
endef

# SSL test: link libevent_openssl + openssl
define SSL_RULE
build/$(1)/$(2): src/$(2).c
	@mkdir -p $$(dir $$@)
	@if [ -f deps/$(1)/lib/libevent_openssl.a ]; then \
		$$(CC) $$(CFLAGS) -o $$@ $$< \
			-I deps/$(1)/include \
			deps/$(1)/lib/libevent_openssl.a \
			deps/$(1)/lib/libevent.a \
			deps/$(1)/lib/libevent_core.a \
			-lssl -lcrypto -lpthread; \
	else \
		echo "[SKIP] $$@ — no libevent_openssl.a for $(1)"; \
	fi
endef

$(foreach v,$(VERSIONS),$(foreach t,$(TESTS_CORE),$(eval $(call CORE_RULE,$(v),$(t)))))
$(foreach v,$(VERSIONS),$(foreach t,$(TESTS_SSL),$(eval $(call SSL_RULE,$(v),$(t)))))

ALL_TARGETS  = $(foreach v,$(VERSIONS),$(foreach t,$(TESTS_CORE),build/$(v)/$(t)))
ALL_TARGETS += $(foreach v,$(VERSIONS),$(foreach t,$(TESTS_SSL),build/$(v)/$(t)))

.PHONY: all clean

all: $(ALL_TARGETS)

clean:
	rm -rf build/
