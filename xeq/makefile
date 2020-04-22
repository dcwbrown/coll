# Rule input $^, rule output $@

# Adapt to Windows executable name convention by defining XE (Executable extension)

.SUFFIXES:

PROJECTS := test

.PHONY: all clean

all: $(PROJECTS)
	-./test$(XE)

ifdef WINDIR
XE=.exe
EXECUTABLES=$(PROJECTS:%=%.exe)
.PHONY: $(PROJECTS)
$(PROJECTS): %: %.exe
PATH:=/d/projects/oberon/vishap/master/install/bin:$(PATH)
else
XE=
EXECUTABLES = $(PROJECTS)
PATH := /opt/voc/bin:$(PATH)
endif

%.o: %.mod
	voc -r -s -OC $^

test$(XE): test.mod TextWriter.o w.o
test$(XE): Codespace.o Codegen.o Functions.o Jobs.o
test$(XE): Prefix.o
test$(XE):
	voc -r -M -OC test.mod


clean:
	rm -f *.c *.h *.o *.sym *.stackdump $(EXECUTABLES)


