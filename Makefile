HC      = ghc
HC_OPTS = -fglasgow-exts
OUT_DIR = out
HI_DIR = hi

SRCS = $(wildcard  *.hs) $(wildcard  Importer/*.hs)  $(wildcard  Importer/*/*.hs)
OBJS = $(SRCS:%.hs=$(OUT_DIR)/%.o)
HIS = $(SRCS:%.hs=$(HI_DIR)/%.hi)

PACKAGES = uniplate base haskell-src-exts
PKGS = $(foreach pkg,$(PACKAGES),-package $(pkg))

.PHONY : clean depend echo
.SUFFIXES : .o .hs .hi .lhs .hc .s


build/importer : $(OBJS)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) -hidir $(HI_DIR) -odir $(OUT_DIR) $(PKGS) $(OBJS)

echo : 
	echo $(PKGS)

clean : 
	rm -f build/importer
	rm -fr $(OUT_DIR)/*
	rm -fr $(HI_DIR)/*

# Standard suffix rules
$(HI_DIR)/%.hi:$(OUT_DIR)/%.o
	@:

#%.o: %.lhs
#	$(HC) -c $< -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

$(OUT_DIR)/%.o: %.hs
	$(HC) -c $< -i$(HI_DIR) -odir $(OUT_DIR) -hidir $(HI_DIR) $(HC_OPTS)

#%.hi-boot : %.o-boot
#	@:

#%.o-boot : %.lhs-boot
#	$(HC) -c $< $(HC_OPTS)

#%.o-boot : %.hs-boot
#	$(HC) -c $< $(HC_OPTS)

depend :
	ghc -M -optdep-f -optdep.depend -fglasgow-exts -odir $(OUT_DIR) -hidir $(HI_DIR) $(SRCS)

-include .depend