# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: all call-install clean extract install

PROJNAME:=Lang
SRCDIR:=theories
SOURCES:=$(shell find $(SRCDIR) -name '*.v')
FLAGS:=-Q $(SRCDIR) $(PROJNAME)
OCAMLMK:=ocaml.mk
MCOQ:=Makefile.coq
EXTRACTV:=Extract.v
COQVERSION:=$$(coqc -print-version | cut -d '.' -f -2)

all: $(MCOQ)
	make -f $< $@

call-install: all
	make -f $(MCOQ) install

extract: call-install $(EXTRACTV)
	mkdir -p $${out}/extracted
	cd $${out} && coqtop -q -w all -Q $${out}/lib/coq/$(COQVERSION)/user-contrib/$(PROJNAME) $(PROJNAME) -batch -load-vernac-source $${src}/$(EXTRACTV)

install: $(OCAMLMK) extract
	cp $< $${out}/extracted/Makefile
	make -C $${out}/extracted

clean: $(MCOQ)
	make -f $< cleanall
	rm -fr _CoqProject .filestoinstall extracted Makefile.coq Makefile.coq.conf result
	find . -name '*.aux' -o -name '*.glob' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm

$(MCOQ): _CoqProject
	coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: $(SRCDIR) Makefile
	echo '$(FLAGS)' > $@
