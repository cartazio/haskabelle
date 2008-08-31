# the haskell compiler to use
HC      = ghc
# the options for the haskell compiler
HC_OPTS = -fglasgow-exts
# the directory to put the object files to
OUT_DIR = out
# the directory to put the interface files to
HI_DIR = hi

# function that takes one argument that is supposed to be a file path
# and returns recursively all .hs and .lhs files contained below this
# path.
search_srcs = \
	$(foreach file, \
		$(wildcard $(1)/*), \
		$(filter %.hs %lhs,$(file)) $(call search_srcs,$(file)) \
	) 
# all source files
SRCS = $(wildcard  *.hs) $(call search_srcs,Importer)
# the corresponding object files
OBJS = $(SRCS:%.hs=$(OUT_DIR)/%.o)
# the corresponding interface files
HIS = $(SRCS:%.hs=$(HI_DIR)/%.hi)

# list of the packages needed
PACKAGES = uniplate base haskell-src-exts
# this is used as a command line argument for ghc to include the 
# packages as stated in the variable PACKAGES
PKGS = $(foreach pkg,$(PACKAGES),-package $(pkg))


.PHONY : clean depend all rebuild
.SUFFIXES : .o .hs .hi .lhs .hc .s

all : build/importer
	@:

build/importer : $(OBJS)
	@rm -f $@
	@$(HC) -o $@ $(HC_OPTS) -hidir $(HI_DIR) -odir $(OUT_DIR) $(PKGS) $(OBJS)

clean : 
	@rm -f build/importer
	@rm -fr $(OUT_DIR)/*
	@rm -fr $(HI_DIR)/*

rebuild : clean all
	@:



# Standard suffix rules
$(HI_DIR)/%.hi:$(OUT_DIR)/%.o
	@:

$(OUT_DIR)/%.o: %.lhs
	@$(HC) -c $< -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o: %.hs
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(HI_DIR)/%.hi-boot : $(OUT_DIR)/%.o-boot
	@:

$(OUT_DIR)/%.o-boot : %.lhs-boot
	@$(HC) -c $< $(HC_OPTS)

$(OUT_DIR)/%.o-boot : %.hs-boot
	@$(HC) -c $< $(HC_OPTS)

# let ghc generate the dependencies
depend :
	@ghc -M -optdep-f -optdep.depend -odir $(OUT_DIR) -hidir $(HI_DIR) $(SRCS)

# include the result
-include .depend