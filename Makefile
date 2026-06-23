CHECKER_SOURCES := \
	src/common/__init__.py \
	src/common/check_proof.py \
	src/common/cheating_detection.py \
	$(shell find src/tlacheck src/tlacore -type f -name '*.py')

.PHONY: setup build clean

check_proof_bin: $(CHECKER_SOURCES)
	uv run --locked pyinstaller --onefile --name check_proof_bin \
		--paths src/common --paths src \
		--collect-submodules tlacheck \
		--collect-submodules tlacore \
		src/common/check_proof.py
	mv dist/check_proof_bin ./check_proof_bin
	rm -rf dist/ build/ check_proof_bin.spec

build: check_proof_bin

setup:
	bash scripts/setup.sh

clean:
	rm -f check_proof_bin
	rm -rf dist/ build/ *.spec
