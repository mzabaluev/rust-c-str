CARGO = cargo

all:
	$(CARGO) build

clean:
	$(CARGO) clean

check:
	$(CARGO) test

.PHONY: all clean check
