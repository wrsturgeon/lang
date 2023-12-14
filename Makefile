# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: all clean

SRCDIR:=theories
SOURCES:=$(shell find $(SRCDIR) -name '*.v')
MCOQ:=Makefile.coq

all install: $(MCOQ)
	+$(MAKE) -f $< $@

clean: $(MCOQ)
	+$(MAKE) -f $< cleanall
	rm -f _CoqProject .filestoinstall Makefile.coq Makefile.coq.conf result
	find . -name '*.aux' -o -name '*.glob' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm

$(MCOQ): _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: $(SRCDIR) Makefile
	echo '-Q $(SRCDIR) Adam' > $@
