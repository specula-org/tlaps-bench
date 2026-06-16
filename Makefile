.PHONY: build clean

check_proof_bin: src/common/check_proof.py src/common/cheating_detection.py
	pyinstaller --onefile --name check_proof_bin \
		--paths src/common --paths src \
		--collect-submodules tlacheck \
		--collect-submodules tlacore \
		src/common/check_proof.py
	mv dist/check_proof_bin ./check_proof_bin
	rm -rf dist/ build/ check_proof_bin.spec

build: check_proof_bin

clean:
	rm -f check_proof_bin
	rm -rf dist/ build/ *.spec
