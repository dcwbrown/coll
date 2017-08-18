# Rule input $^, rule output $@

PATH := /d/projects/oberon/vishap/master/install/bin:$(PATH)

target := coll

.PHONY: all
.PHONY: clean

all: $(target).exe
	./$(target).exe

sublime: $(target).exe
	mintty ./$(target).exe


%.exe: %.mod
	voc -r -m $^

clean:
	rm -f *.exe


