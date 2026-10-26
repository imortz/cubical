# cubical
#
#   make            ./cubical, cloning and building CaDiCaL first if
#                   third_party/cadical is absent
#   make debug      ./cubical-debug, with ASan and UBSan
#   make clean      remove cubical's build products
#   make distclean  also remove third_party/
#
# cubical links CaDiCaL statically through IPASIR and needs its headers and
# libcadical.a, which distribution packages do not ship.  CADICAL_DIR names a
# checkout to use instead of cloning one; it is configured and built in place
# if it has no build/libcadical.a.  IPASIR_INC and IPASIR_LIB override the
# include and library paths separately.

CADICAL_REPO    ?= https://github.com/arminbiere/cadical.git
CADICAL_VERSION ?= rel-3.0.1
CADICAL_DIR     ?= third_party/cadical

IPASIR_INC ?= $(CADICAL_DIR)/src
IPASIR_LIB ?= $(CADICAL_DIR)/build/libcadical.a

CC       ?= gcc
CXX      ?= g++
CFLAGS   ?= -Wall -Wextra -O2 -g
CXXFLAGS ?= -Wall -Wextra -O2 -g
LDLIBS   += -lstdc++ -lm

# -fno-sanitize=vptr: cshim.cpp reinterprets ccadical_init()'s opaque pointer
# as a ShimWrapper, which the RTTI check reports on every call.  The layout is
# verified at startup against ccadical_fixed().
#
# -U_FORTIFY_SOURCE: the debug build is -O0, which _FORTIFY_SOURCE warns
# about.  No effect where the toolchain appends its own flags after these.
SAN = -fsanitize=address,undefined -fno-sanitize=vptr -U_FORTIFY_SOURCE

all: cubical

cubical: cubical.c cshim.cpp $(IPASIR_LIB)
	$(CXX) $(CXXFLAGS) -I$(IPASIR_INC) -c cshim.cpp -o cshim.o
	$(CC) $(CFLAGS) -I$(IPASIR_INC) cubical.c cshim.o $(IPASIR_LIB) \
	    -o $@ $(LDLIBS)

# Its own name, so a sanitiser build is not left behind as ./cubical.
cubical-debug: cubical.c cshim.cpp $(IPASIR_LIB)
	$(CXX) -Wall -Wextra -O0 -g $(SAN) -I$(IPASIR_INC) \
	    -c cshim.cpp -o cshim-debug.o
	$(CC) -Wall -Wextra -O0 -g $(SAN) -I$(IPASIR_INC) \
	    cubical.c cshim-debug.o $(IPASIR_LIB) -o $@ $(LDLIBS)

debug: cubical-debug

# Only reached when the library is absent, so an existing checkout is never
# re-cloned and a built one is left alone.
#
# The guard is on configure, not on the directory.  A clone that failed or was
# interrupted -- a cluster login node with no outbound HTTPS is the usual way --
# leaves the directory behind, and a directory test then skips the retry on
# every later make and falls through to a ./configure that was never fetched.
# That wedges the tree permanently and reports it as "./configure: No such file
# or directory", which names neither the cause nor the cure.
#
# The stale directory is not removed here: CADICAL_DIR is overridable, and a
# recursive delete of a path this file did not choose is not something a build
# should do behind the caller's back.  Say what to remove and stop.
$(CADICAL_DIR)/build/libcadical.a:
	@if [ ! -x "$(CADICAL_DIR)/configure" ]; then \
	    if [ -e "$(CADICAL_DIR)" ]; then \
	        echo "$(CADICAL_DIR) exists but has no configure in it, so an"; \
	        echo "earlier clone did not finish.  Remove it and run make again:"; \
	        echo "    rm -rf $(CADICAL_DIR)"; \
	        exit 1; \
	    fi; \
	    echo "==> cloning CaDiCaL $(CADICAL_VERSION) into $(CADICAL_DIR)"; \
	    git clone --depth 1 --branch "$(CADICAL_VERSION)" \
	        "$(CADICAL_REPO)" "$(CADICAL_DIR)"; \
	fi
	@echo "==> building CaDiCaL in $(CADICAL_DIR)"
	cd "$(CADICAL_DIR)" && ./configure
	$(MAKE) -C "$(CADICAL_DIR)/build" libcadical.a

# An overridden IPASIR_LIB that does not exist is a wrong path, not a target
# to build.
ifneq ($(IPASIR_LIB),$(CADICAL_DIR)/build/libcadical.a)
ifeq ($(wildcard $(IPASIR_LIB)),)
$(error IPASIR_LIB=$(IPASIR_LIB) does not exist)
endif
endif

clean:
	rm -f cubical cubical-debug cshim.o cshim-debug.o

distclean: clean
	rm -rf third_party

.PHONY: all debug clean distclean
