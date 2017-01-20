WS := "-w -notation-overridden,-redundant-canonical-projection"

default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -arg $(WS) -f _CoqProject > Makefile.coq

.PHONY: default clean
