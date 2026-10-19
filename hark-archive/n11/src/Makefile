PYTHON ?= python

.PHONY: verify restore check-math-n11 check-math-n12 check-math-n12-quick test-math gallery test-assets restore-core-n23-n25 restore-n11-wip restore-n11-supplement restore-replay-n21-n22 restore-replay-n23-n25
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

test-assets:
	$(PYTHON) tools/test_frozen_assets.py

# Frozen bytes only. The mathematical core dispatcher is still pending.
restore-core-n23-n25:
	$(PYTHON) tools/restore_frozen_assets.py --package-index assets/replay/n23-n25-core/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-core-20261014 --destination build/core-assets

restore-n11-wip:
	$(PYTHON) tools/restore_frozen_assets.py --package-index assets/replay/n11-wip/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-core-20261014 --destination build/n11-wip

restore-n11-supplement:
	$(PYTHON) tools/restore_frozen_assets.py --package-index assets/replay/n11-supplement/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-replay-20261014 --destination build/n11-wip

restore-replay-n21-n22:
	$(PYTHON) tools/restore_frozen_assets.py --package-index assets/replay/n21-n22/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-replay-20261014 --destination build/n21-n22-assets

restore-replay-n23-n25:
	$(PYTHON) tools/restore_frozen_assets.py --package-index assets/replay/n23-n25-full/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-replay-20261014 --destination build/n23-n25-assets
