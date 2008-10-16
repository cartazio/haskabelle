#############
# variables #
#############

# the haskell compiler to use
HC      = ghc
# the options for the haskell compiler
HC_OPTS = -fglasgow-exts
# source directory
SRC_DIR = .
# the directory to put the object files to
OUT_DIR = build/out/default
# the directory to put the hpc object files to
COUT_DIR = build/out/hpc
# the directory to put the optimised object files to
OOUT_DIR = build/out/optimised
# the directory to put the interface files to
HI_DIR = build/hi/default
# the directory to put the interface files for hpc compiling to
CHI_DIR = build/hi/hpc
# the directory to put the interface files for optimised compiling to
OHI_DIR = build/hi/optimised
# the directory to put the interface documentation to
HADDOCK_DIR = haddock/interface
# the directory to put the implementation documentation to
HADDOCK_IMPL_DIR = haddock/impl
# the directory to put the built binaries to
BUILD_DIR = build/bin
# the filename for the default binary
BIN_NAME = importer
# the filename for the hpc binary
CBIN_NAME = imp-hpc
# the filename for the optimised binary
OBIN_NAME = imp
# the hpc directory
HPC_DIR = build/mix
# the hpc markup directory
HPC_MARKUP_DIR = hpc/default
# hpc flags (only used for the "hpc" target)
CFLAGS = -fhpc -hpcdir $(HPC_DIR)
# optimisation flags (only used for the "optimised" target)
OFLAGS = -O2

################################
# derived variable / functions #
################################

# function that takes one argument that is supposed to be a file path
# and returns recursively all .hs and .lhs files contained below this
# path.
search_srcs = \
	$(foreach file, \
		$(wildcard $(1)/*), \
		$(filter %.hs %lhs,$(file)) $(call search_srcs,$(file)) \
	) 


# this function looks up the given field (2nd arg) of the given package (1st arg)
get-field = $(word 2, $(shell ghc-pkg field $(1) ))

# all source files
SRCS = $(wildcard  $(SRC_DIR)/*.hs) $(call search_srcs,$(SRC_DIR)/Importer) $(call search_srcs,$(SRC_DIR)/Data)
# the corresponding object files
OBJS = $(SRCS:$(SRC_DIR)/%.hs=$(OUT_DIR)/%.o)
# the corresponding hpc object files
COBJS = $(SRCS:$(SRC_DIR)/%.hs=$(COUT_DIR)/%.o)
# the corresponding optimised object files
OOBJS = $(SRCS:$(SRC_DIR)/%.hs=$(OOUT_DIR)/%.o)

# a list of all directories that might need to be created
ALL_DIRS = $(HADDOCK_DIR) $(HADDOCK_IMPL_DIR) $(BUILD_DIR) $(HI_DIR) $(CHI_DIR) $(OHI_DIR) $(OUT_DIR) $(COUT_DIR) $(OOUT_DIR) $(HPC_MARKUP_DIR)
# list of the packages needed
PACKAGES = uniplate base haskell-src-exts QuickCheck-2.0 template-haskell xml
# list of packages to exclude for hadock
EXCL_PGK_HADDOCK = haskell-src-exts
# this is used as a command line argument for ghc to include the 
# packages as stated in the variable PACKAGES
PKGS = $(foreach pkg,$(PACKAGES),-package $(pkg))
# list of packages used for haddock
PKG_HADDOCK = $(foreach pkg,$(filter-out $(EXCL_PGK_HADDOCK),$(PACKAGES)),--read-interface=$(call get-field, $(pkg) haddock-html),$(call get-field, $(pkg) haddock-interfaces) )


################
# declarations #
################

.PHONY : clean clean-optimised clean-hpc build rebuild rebuild-hpc rebuild-optimised depend-default depend-hpc depend-optimised hpc-markup
.SUFFIXES : .o .hs .hi .lhs .hc .s

#######################
# compilation targets #
#######################

# builds the default binary
default : $(BUILD_DIR)/$(BIN_NAME)
	@:

# builds the hpc binary
hpc : $(BUILD_DIR)/$(CBIN_NAME)
	@:

# builds the optimised binary
optimised : $(BUILD_DIR)/$(OBIN_NAME)
	@:

# builds all binaries and haddock documentations
all : hpc default optimised haddock haddock-impl
	@:

# rebuilds all binaries and haddock documentations
rebuild-all : clean-all all
	@:

# builds the hpc binary
$(BUILD_DIR)/$(CBIN_NAME) : $(COBJS) $(BUILD_DIR)
	@rm -f $@
	@echo linking hpc binary ...
	@$(HC) -o $@ $(HC_OPTS) -hidir $(CHI_DIR) -odir $(COUT_DIR) $(PKGS) $(COBJS) $(CFLAGS)

# builds the optimised binary
$(BUILD_DIR)/$(OBIN_NAME) :  $(OOBJS) $(BUILD_DIR)
	@rm -f $@
	@echo linking optimised binary ...
	@$(HC) -o $@ $(HC_OPTS) -hidir $(OHI_DIR) -odir $(OOUT_DIR) $(PKGS) $(OOBJS) $(OFLAGS)

# builds the default binary
$(BUILD_DIR)/$(BIN_NAME) : $(OBJS) $(BUILD_DIR)
	@rm -f $@
	@echo linking default binary ...
	@$(HC) -o $@ $(HC_OPTS) -hidir $(HI_DIR) -odir $(OUT_DIR) $(PKGS) $(OBJS)

# cleans all binaries and haddock documentations
clean-all : clean clean-optimised clean-haddock clean-haddock-impl clean-hpc
	@:

# cleans the hpc compilation
clean-hpc:
	@echo cleaning hpc build ...
	@rm -f  $(BUILD_DIR)/$(CBIN_NAME)
	@rm -fr $(COUT_DIR)/*
	@rm -fr $(CHI_DIR)/*

# cleans the optimised compilation
clean-optimised:
	@echo cleaning optimised build ...
	@rm -f  $(BUILD_DIR)/$(OBIN_NAME)
	@rm -fr $(OOUT_DIR)/*
	@rm -fr $(OHI_DIR)/*

# cleans the default compilaton
clean : 
	@echo cleaning default build ...
	@rm -f  $(BUILD_DIR)/$(BIN_NAME)
	@rm -fr $(OUT_DIR)/*
	@rm -fr $(HI_DIR)/*

# rebuilds the hpc binary
rebuild-hpc : clean-hpc hpc
	@:

# rebuilds the optimised binary
rebuild-optimised : clean-optimised optimised
	@:

# rebuilds the default binary
rebuild : clean default
	@:
#########################
# Standard suffix rules #
#########################


$(HI_DIR)/%.hi : $(OUT_DIR)/%.o $(HI_DIR)
	@:

$(CHI_DIR)/%.hi : $(COUT_DIR)/%.o $(CHI_DIR)
	@:

$(OHI_DIR)/%.hi : $(OOUT_DIR)/%.o $(OHI_DIR)
	@:

$(OUT_DIR)/%.o: %.lhs $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o: %.hs  $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(COUT_DIR)/%.o: %.lhs $(COUT_DIR)
	@echo hpc compiling $< ...
	@$(HC) -c $< -i$(CHI_DIR) -odir $(COUT_DIR) -hidir $(CHI_DIR) $(HC_OPTS) $(CFLAGS)

$(COUT_DIR)/%.o: %.hs $(COUT_DIR)
	@echo hpc compiling $< ...
	@$(HC) -c $< -i$(CHI_DIR) -odir $(COUT_DIR) -hidir $(CHI_DIR) $(HC_OPTS) $(CFLAGS)

$(OOUT_DIR)/%.o: %.lhs $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(OOUT_DIR)/%.o: %.hs $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(HI_DIR)/%.hi-boot : $(OUT_DIR)/%.o-boot $(HI_DIR)
	@:

$(CHI_DIR)/%.hi-boot : $(COUT_DIR)/%.o-boot $(CHI_DIR)
	@:

$(OHI_DIR)/%.hi-boot : $(OOUT_DIR)/%.o-boot $(OHI_DIR)
	@:

$(OUT_DIR)/%.o-boot: %.lhs-boot $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o-boot: %.hs-boot $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(COUT_DIR)/%.o-boot: %.lhs-boot $(COUT_DIR)
	@echo hpc compiling $< ...
	@$(HC) -c $< -i$(CHI_DIR) -odir $(COUT_DIR) -hidir $(CHI_DIR) $(HC_OPTS) $(CFLAGS)

$(COUT_DIR)/%.o-boot: %.hs-boot $(COUT_DIR)
	@echo hpc compiling $< ...
	@$(HC) -c $< -i$(CHI_DIR) -odir $(COUT_DIR) -hidir $(CHI_DIR) $(HC_OPTS) $(CFLAGS)

$(OOUT_DIR)/%.o-boot: %.lhs-boot $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(OOUT_DIR)/%.o-boot: %.hs-boot $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

###############
# HPC targets #
###############

hpc-markup : $(HPC_MARKUP_DIR)
	@echo creating hpc markup
	@hpc markup --srcdir=$(SRC_DIR) --hpcdir=$(HPC_DIR) --destdir=$(HPC_MARKUP_DIR) $(CBIN_NAME)

###################
# Haddock targets #
###################

# builds standard interface documentation
haddock : $(HADDOCK_DIR) $(SRCS)
	@echo generating interface haddock ...
	@haddock -o $(HADDOCK_DIR) -h -t "Hsimp" $(PKG_HADDOCK) \
	--optghc=$(HC_OPTS) \
	--optghc=-i$(HI_DIR) \
	--optghc=-odir --optghc=$(OUT_DIR) \
	--optghc=-hidir --optghc=$(HI_DIR) \
	$(filter-out %Raw.hs , $(SRCS))

# builds an implementation documentation, i.e. including also elements that are not exported
haddock-impl : $(HADDOCK_IMPL_DIR) $(SRCS)
	@echo generating implementation haddock ...
	@haddock -o $(HADDOCK_IMPL_DIR) -h --ignore-all-exports -t "Hsimp" $(PKG_HADDOCK) \
	--optghc=$(HC_OPTS) \
	--optghc=-i$(HI_DIR) \
	--optghc=-odir --optghc=$(OUT_DIR) \
	--optghc=-hidir --optghc=$(HI_DIR) \
	$(filter-out %Raw.hs , $(SRCS))

clean-haddock :
	@echo cleaning interface haddock ...
	@rm -fr $(HADDOCK_DIR)/*

clean-haddock-impl :
	@echo cleaning implementation haddock ...
	@rm -fr $(HADDOCK_IMPL_DIR)/*

rehaddock : clean-haddock haddock
	@:

rehaddock-impl : clean-haddock-impl haddock-impl
	@:

########
# misc #
########

# builds directories
$(ALL_DIRS) : 
	@echo creating directory $@ ...
	@mkdir -p $@

# let ghc generate the dependencies
depend : depend-default depend-optimised depend-hpc
	@:

depend-hpc : $(COUT_DIR) $(CHI_DIR)
	@echo analysing dependencies ...
	@ghc -M -optdep-f -optdep.depend-hpc -odir $(COUT_DIR) -hidir $(CHI_DIR) $(SRCS)

depend-optimised : $(OOUT_DIR) $(OHI_DIR)
	@echo analysing dependencies ...
	@ghc -M -optdep-f -optdep.depend-optimised -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(SRCS)

depend-default : $(OUT_DIR) $(HI_DIR)
	@echo analysing dependencies ...
	@ghc -M -optdep-f -optdep.depend-default -odir $(OUT_DIR) -hidir $(HI_DIR) $(SRCS)

# include the result
-include .depend-default
-include .depend-hpc
-include .depend-optimised