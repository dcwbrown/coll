# Rule input $^, rule output $@

PATH := /d/projects/oberon/vishap/master/install/bin:$(PATH)


.PHONY: all
.PHONY: clean

all: geli.exe fol.exe coll.exe PrefixMap.exe brace.exe folio.exe

folio: folio.exe
	-./folio.exe

brace: brace.exe
	-./brace.exe

geli: geli.exe
	-./geli.exe

fol: fol.exe
	-./fol.exe

coll: coll.exe
	mintty ./coll.exe

prefixmap: PrefixMap.exe
	./PrefixMap.exe

%.o: %.mod
	voc -r -OC $^

folio.exe: folio.mod TextWriter.o
	voc -r -m -OC folio.mod

brace.exe: brace.mod TextWriter.o
	voc -r -M brace.mod

geli.exe: geli.mod TextWriter.o
	voc -r -M geli.mod

fol.exe: fol.mod TextWriter.o
	voc -r -M fol.mod

coll.exe: coll.mod
	voc -r -m $^

PrefixMap.exe: PrefixMap.mod
	voc -r -m $^

clean:
	rm -f *.exe *.c *.h *.o *.sym *.stackdump





# # Rule input $^, rule output $@
#
# PATH := /d/projects/oberon/vishap/master/install/bin:$(PATH)
#
# target := coll
#
# .PHONY: all
# .PHONY: clean
#
# all: $(target).exe
# 	./$(target).exe
#
# sublime: $(target).exe
# 	mintty ./$(target).exe
#
#
# %.exe: %.mod
# 	voc -r -m $^
#
# clean:
# 	rm -f *.exe


