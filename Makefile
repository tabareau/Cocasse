COQDOCOPTS=--utf8 -g --interpolate --body-only -R . Casts -coqlib http://coq.inria.fr/stdlib/ 
COQOPTS=
COQBIN=

all: coqcompile ${TARGETS} 

coqcompile:
	coq_makefile -R . Casts *.v -o Makefile_coq
	$(MAKE) -f Makefile_coq > \dev\null

%.vo: %.v
	${COQBIN}coqc ${COQOPTS} $<

clean: 
	$(MAKE) -f Makefile_coq clean
	rm -f ${TARGETS}
