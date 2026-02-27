# Contributing to HCIspecs

HCIspecs is a curated repository of interaction models used in research and teaching.
All submissions are reviewed before publication to ensure consistency, completeness, and long-term maintainability.

---

## Overview

Models are submitted via Pull Request (GitHub).

1. Fork the repository (or create a branch if you have access).
2. Add your model metadata file under `_models/`.
3. Add associated files under `assets/models/`.
4. Open a Pull Request.
5. The submission will be reviewed before being merged.

Publications, tools, and contributor records may only be introduced as part of a model submission.

---

## Repository Structure

### Model Metadata

Each model must have a metadata file in: `_models/`

Example filename: `_models/m-temp-example.md`

The file must contain valid YAML frontmatter.

Use the template in: `_templates/model.md`

---

### Model Assets

All model files must be placed under: `assets/models/<record_id>/`

Example:

```
assets/models/M-TEMP-EXAMPLE/
  M-TEMP-EXAMPLE_v1.0.zip
  thumb.png   (optional)
```

---

## Record IDs

Contributors should use a temporary identifier such as: `M-TEMP-<shortname>`

The final record ID (e.g., `M-0000`) will be assigned during review.

Do not manually assign numeric IDs.

---

## Required Metadata Fields

Each submission must include:

- record_id
- name
- description
- submitted_by
- tool
- language
- At least one entry under versions

Optional fields:

- publications

---

## Versions

Each model must include at least one version entry:

```
versions:
  - version: "1.0"
    date: 2026-01-01T00:00:00Z
    label: "Initial release"
    file: /assets/models/M-TEMP/M-TEMP_v1.0.zip
```

The file path must match the actual file location.

---

## Authors / Tools / Publications

If the model is associated with authors/tools/publications already in the repository,
include their record IDs under:

### Authors

```
- submitted_by
  - "U-0000"
  - "U-0010"
```

### Tool

```
- tool: "T-0000"
- language: "the tool's language"
```

### Publications

```
publications:
  - "P-0000"
```

### New Authors / Tools / Publications

If an author, tool, or publication is not yet present in the repository, include a corresponding metadata file in the appropriate collection (`_people/`, `_tools/`, `_publications/`) as part of the same Pull Request. 
Temporary record IDs must follow the same TEMP convention (e.g., `U-TEMP-DOE`, `T-TEMP-XYZ`, `P-TEMP-ABC`).

---

## Validation

Before opening a Pull Request, please:

- Verify metadata fields are complete
- Ensure filenames and paths are correct

---

## Review Process

Submissions are reviewed for:

- Structural correctness
- Metadata completeness
- Consistency with repository conventions
- Proper file organization
- Licensing clarity

The maintainers may request revisions before merging.

---

## Licensing

Contributors must ensure they have the right to distribute submitted materials.

If the model includes third-party content, appropriate permissions must be documented.

---

## Need Help?

If you are unfamiliar with Git or the submission process,
please contact the maintainers for assistance.

---

Thank you for helping maintain a high-quality repository of interaction models.