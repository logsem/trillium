TRILLIUM_DIR := 'trillium'
HL_DIR := 'heap_lang'
FAIRNESS_DIR := 'fairness'
FAIRIS_DIR := 'fairis'
SRC_DIRS := $(TRILLIUM_DIR) $(FAIRNESS_DIR) $(HL_DIR) $(FAIRIS_DIR)

VFILES := $(shell find $(SRC_DIRS) -name "*.v")

COQC := coqc
Q:=@

# extract global arguments for Coq from _CoqProject
COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)

all: $(VFILES:.v=.vo)

.coqdeps.d: $(VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(VFILES) > $@

# do not try to build dependencies if cleaning or just building _CoqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
include .coqdeps.d
endif

%.vo: %.v _CoqProject | .coqdeps.d
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vok $(COQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	rm -f .coqdeps.d

# project-specific targets
.PHONY: build clean-trillium trillium clean-fairness fairness clean-heap-lang heap-lang clean-fairis fairis

VPATH= $(TRILLIUM_DIR) $(FAIRNESS_DIR) $(HL_DIR) $(FAIRIS_DIR)
VPATH_FILES := $(shell find $(VPATH) -name "*.v")

build: $(VPATH_FILES:.v=.vo)

trillium :
	@$(MAKE) build VPATH=$(TRILLIUM_DIR)

fairness :
	@$(MAKE) build VPATH=$(FAIRNESS_DIR)

heap-lang :
	@$(MAKE) build VPATH=$(HL_DIR)

fairis :
	@$(MAKE) build VPATH=$(FAIRIS_DIR)

clean-trillium:
	@$(MAKE) clean SRC_DIRS=$(TRILLIUM_DIR)

clean-fairness:
	@$(MAKE) clean SRC_DIRS=$(FAIRNESS_DIR)

clean-heap-lang:
	@$(MAKE) clean SRC_DIRS=$(HL_DIR)

clean-fairis:
	@$(MAKE) clean SRC_DIRS=$(FAIRIS_DIR)
