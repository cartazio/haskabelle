#############
# variables #
#############

# the haskell compiler to use
HC      = ghc
# the options for the haskell compiler
HC_OPTS = -fglasgow-exts
# the directory to put the object files to
OUT_DIR = build/out/default
# the directory to put the optimised object files to
OOUT_DIR = build/out/optimised
# the directory to put the interface files to
HI_DIR = build/hi/default
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
# the filename for the optimised binary
OBIN_NAME = imp
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
SRCS = $(wildcard  *.hs) $(call search_srcs,Importer)
# the corresponding object files
OBJS = $(SRCS:%.hs=$(OUT_DIR)/%.o)
# the corresponding optimisedd object files
OOBJS = $(SRCS:%.hs=$(OOUT_DIR)/%.o)
# the corresponding interface files
HIS = $(SRCS:%.hs=$(HI_DIR)/%.hi)

# a list of all directories that might need to be created
ALL_DIRS = $(HADDOCK_DIR) $(HADDOCK_IMPL_DIR) $(BUILD_DIR) $(HI_DIR) $(OHI_DIR) $(OUT_DIR) $(OOUT_DIR)
# list of the packages needed
PACKAGES = uniplate base haskell-src-exts
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

.PHONY : clean clean-optimised build rebuild rebuild-optimised depend-default depend-optimised echo
.SUFFIXES : .o .hs .hi .lhs .hc .s

#######################
# compilation targets #
#######################

echo : 
	@echo $(PKG_HADDOCK)

# builds the default binary
default : $(BUILD_DIR)/$(BIN_NAME)
	@:

# builds the optimised binary
optimised : $(BUILD_DIR)/$(OBIN_NAME)
	@:

# builds all binaries and haddock documentations
all : default optimised haddock haddock-impl
	@:

# rebuilds all binaries and haddock documentations
rebuild-all : clean-all all
	@:

# builds the optimised binary
$(BUILD_DIR)/$(OBIN_NAME) : depend-optimised $(OOBJS) $(BUILD_DIR)
	@rm -f $@
	@echo linking optimised binary ...
	@$(HC) -o $@ $(HC_OPTS) -hidir $(OHI_DIR) -odir $(OOUT_DIR) $(PKGS) $(OOBJS) $(OFLAGS)

# builds the default binary
$(BUILD_DIR)/$(BIN_NAME) : depend-default $(OBJS) $(BUILD_DIR)
	@rm -f $@
	@echo linking default binary ...
	@$(HC) -o $@ $(HC_OPTS) -hidir $(HI_DIR) -odir $(OUT_DIR) $(PKGS) $(OBJS)

# cleans all binaries and haddock documentations
clean-all : clean clean-optimised clean-haddock clean-haddock-impl
	@:

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

$(OHI_DIR)/%.hi : $(OOUT_DIR)/%.o $(OHI_DIR)
	@:

$(OUT_DIR)/%.o: %.lhs $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o: %.hs  $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OOUT_DIR)/%.o: %.lhs $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(OOUT_DIR)/%.o: %.hs $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(HI_DIR)/%.hi-boot : $(OUT_DIR)/%.o-boot $(HI_DIR)
	@:

$(OHI_DIR)/%.hi-boot : $(OOUT_DIR)/%.o-boot $(OHI_DIR)
	@:

$(OUT_DIR)/%.o-boot: %.lhs-boot $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o-boot: %.hs-boot $(OUT_DIR)
	@echo compiling $< ...
	@$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OOUT_DIR)/%.o-boot: %.lhs-boot $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)

$(OOUT_DIR)/%.o-boot: %.hs-boot $(OOUT_DIR)
	@echo optimised compiling $< ...
	@$(HC) -c $< -i$(OHI_DIR) -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(HC_OPTS) $(OFLAGS)


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
depend : depend-default depend-optimised
	@:

depend-optimised : $(OOUT_DIR) $(OHI_DIR)
	@echo analysing dependencies ...
	@ghc -M -optdep-f -optdep.depend-optimised -odir $(OOUT_DIR) -hidir $(OHI_DIR) $(SRCS)

depend-default : $(OUT_DIR) $(HI_DIR)
	@echo analysing dependencies ...
	@ghc -M -optdep-f -optdep.depend-default -odir $(OUT_DIR) -hidir $(HI_DIR) $(SRCS)

# include the result
-include .depend-default
-include .depend-optimised