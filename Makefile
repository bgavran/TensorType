export HEDGEHOG_COLOR=1

.PHONY: all build install examples test clean

all: build

build:
	pack build tensortype.ipkg

install:
	pack install tensortype

examples:
	cd examples && pack --no-prompt install tensortype-examples

test: build examples
	pack test tensortype

clean:
	pack clean tensortype
	cd examples && pack clean && cd ..
	cd tests && pack clean && cd ..

