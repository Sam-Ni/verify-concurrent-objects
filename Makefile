COQMKFILENAME=CoqSrc.mk

LIBNAME=VCO

.PHONY: all clean coq 

all: coq

%.mk : Makefile _%
	coq_makefile -f _$* -o $*.mk

$(COQMKFILENAME): Makefile
	{ echo "-R . $(LIBNAME) " ; ls *.v ; } > _CoqProject && coq_makefile -f _CoqProject -o $(COQMKFILENAME)

coq: $(COQMKFILENAME)
	@$(MAKE) -f $(COQMKFILENAME)

clean:
	@$(MAKE) -f $(COQMKFILENAME) clean
	rm -if $(COQMKFILENAME)
	rm -if "$(COQMKFILENAME).conf"
	rm -rf .lia.cache
	rm -rf .*.aux
	rm -rf _CoqProject