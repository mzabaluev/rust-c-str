CARGO = cargo

all:
	$(CARGO) build

clean:
	$(CARGO) clean

check: all
	$(CARGO) test

.PHONY: all clean check
