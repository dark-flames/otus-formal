default: all

all: 
	agda -i src/ src/Entry.agda
.PHONY: all

clean:
	rm -rf _build/
.PHONY: clean