PYTHON ?= python

.PHONY: verify restore check-math-n11 check-math-n12 check-math-n12-quick test-math gallery
verify:
	$(PYTHON) tools/verify_delivery.py

restore:
	$(PYTHON) tools/restore_large_files.py --destination ../restored

# Fresh mathematical arithmetic, not historical acceptance or file hashes.
check-math-n11:
	$(PYTHON) tools/check_math.py n11

check-math-n12:
	$(PYTHON) tools/check_math.py n12

check-math-n12-quick:
	$(PYTHON) tools/check_math.py n12 --quick

test-math:
	$(PYTHON) tools/test_math_checks.py

gallery:
	$(PYTHON) tools/generate_gallery.py
