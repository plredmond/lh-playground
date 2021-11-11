# this file assumes you're already in a nix-shell
#
# this file build using setup commands (not nix-build)

CABAL_FILE = lh-playground.cabal

CONFIG_FILE = dist/setup-config
SETUP_CMD = runhaskell -hide-package=base Setup.hs

.PHONY: test build clean repl

test: build
	$(SETUP_CMD) test

# TODO use dist/build/%/% ? scan cabalfile for executable names?
build: $(CONFIG_FILE)
	$(SETUP_CMD) build

$(CONFIG_FILE): $(CABAL_FILE)
	$(SETUP_CMD) configure --enable-tests

clean: $(CABAL_FILE)
	$(SETUP_CMD) clean
	rm -v $(CABAL_FILE)
	-find . -name '.liquid' -exec rm -rfv '{}' \;

%.cabal: package.yaml
	hpack

## tools

repl: $(CONFIG_FILE)
	$(SETUP_CMD) repl $(basename $(CABAL_FILE))

ghcid:
	nix-shell -p ghcid --run 'ghcid -c make repl'
entr-build:
	git ls-files | entr -c bash -c 'make build; echo done'
entr-test:
	git ls-files | entr -c bash -c 'make test; echo done'
