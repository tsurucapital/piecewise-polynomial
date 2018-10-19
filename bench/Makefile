.PHONY: all clean
all: bench
clean:
	rm -f bench bench.hi bench.o

%: %.hs
	ghc -O2 --make $<

