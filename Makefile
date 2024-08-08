AGDA = agda +RTS -M6G -RTS
PANDOC = pandoc
FIX_WHITESPACE = fix-whitespace

# Finds all .agda or .lagda.* files in the current directory and subdirectories
FIND_AGDA_FILES = find . \( -name "*.agda" -o -name "*.lagda.*" \)
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)

.PHONY: all
all: test check-whitespace check-line-lengths

.PHONY: test
test: Everything.agda
	$(AGDA) $<

html: Everything.agda
	$(AGDA) --html --html-dir='$@' --highlight-occurrences --html-highlight=auto '$<'
	find '$@' -name '*.md' -exec bash -c "$(PANDOC) -f markdown '{}' -t html -o '$@'/Gluing.Conservativity.html --embed-resources --standalone --css='$@'/Agda.css --include-in-header=<(echo '<script>'; cat '$@'/highlight-hover.js; echo '</script>')" \;

.PHONY: test-and-report
test-and-report:
	@failed=""; \
	for file in $(AGDA_FILES); do \
		$(AGDA) $$file || failed="$$failed $$file"; \
	done; \
	[ -z "$$failed" ] || (echo "Failed to compile:$$failed" && false)

.PHONY: check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

.PHONY: check-line-lengths
check-line-lengths:
	bash check-line-lengths.sh

# modified from
# https://github.com/agda/agda-categories/blob/dc2a5bd7ad39b0629b21763884b8e85a96111981/Makefile#L14
#
# NOTES:
# sed: we're using Basic Regular Expression (BRE) syntax
# sort: LC_ALL=C for a deterministic order
# PHONY in case agda files are created/deleted
.PHONY: Everything.agda
Everything.agda:
	$(FIND_AGDA_FILES) ! -path './$@' | sed -e 's#/#.#g' -e 's/^\.*//' -e 's/\.agda$$//' -e 's/\.lagda\..*$$//' -e 's/^/import /' | LC_ALL=C sort > $@

.PHONY: clean
clean:
	find . -name "*.agdai" -type f -delete
	-rm Everything.agda
