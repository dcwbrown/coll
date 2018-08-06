# Rule input $^, rule output $@

# Adapt to Windows executable name convention by defining XE (Executable extension)

.SUFFIXES:

PROJECTS := geli fol coll PrefixMap brace folio hippo panda pad das dam

.PHONY: all clean

all: $(PROJECTS)

ifdef WINDIR
  XE=.exe
  EXECUTABLES = $(PROJECTS:%=%.exe)
  .PHONY: $(PROJECTS)
  $(PROJECTS): %: %.exe
  PATH := /d/projects/oberon/vishap/master/install/bin:$(PATH)
else
	XE=
	EXECUTABLES = $(PROJECTS)
	PATH := /opt/voc/bin:$(PATH)
endif

prefixmap: PrefixMap$(XE)
	./PrefixMap$(XE)

%.o: %.mod
	voc -r -OC $^

dam$(XE): dam.mod TextWriter.o
	voc -r -M -OC dam.mod
	-./dam$(XE)

das$(XE): das.mod TextWriter.o
	voc -r -M -OC das.mod
	-./das$(XE)

pad$(XE): pad.mod TextWriter.o
	voc -r -M -OC pad.mod
	-./pad$(XE)

panda$(XE): panda.mod TextWriter.o
	voc -r -M -OC panda.mod
	-./panda$(XE)

hippo$(XE): hippo.mod TextWriter.o
	voc -r -M -OC hippo.mod
	-./hippo$(XE)

folio$(XE): folio.mod TextWriter.o
	voc -r -m -OC folio.mod
	-./folio$(XE)

brace$(XE): brace.mod TextWriter.o
	voc -r -M brace.mod
	-./brace$(XE)

geli$(XE): geli.mod TextWriter.o
	voc -r -M geli.mod
	-./geli$(XE)

fol$(XE): fol.mod TextWriter.o
	voc -r -M fol.mod
	-./fol$(XE)

coll$(XE): coll.mod
	voc -r -m $^
	mintty ./coll$(XE)

PrefixMap$(XE): PrefixMap.mod
	voc -r -m $^

clean:
	rm -f *.c *.h *.o *.sym *.stackdump $(EXECUTABLES)


