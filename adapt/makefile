# Rule input $^, rule output $@

# Adapt to Windows executable name convention by defining XE (Executable extension)

.SUFFIXES:

PROJECTS := test

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

%.o: %.mod
	voc -r -s -OC $^

test$(XE): test.mod TextWriter.o w.o a.o
test$(XE): bootstrap.o interpreter.o
test$(XE): dumping.o reorganise.o
test$(XE): *.boot
test$(XE):
	voc -r -M -OC test.mod
	-./test$(XE)


clean:
	rm -f *.c *.h *.o *.sym *.stackdump $(EXECUTABLES)


