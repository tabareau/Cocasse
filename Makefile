COQOPTS=
COQBIN=

all: coqcompile ${TARGETS} 

coqcompile:
	coq_makefile -R . Casts *.v -o Makefile_coq
	$(MAKE) -f Makefile_coq > /dev/null

%.vo: %.v
	${COQBIN}coqc ${COQOPTS} $<

clean: 
	$(MAKE) -f Makefile_coq clean
	rm -f ${TARGETS}
