<!--
Copyright 2022 Thales DIS Design Services SAS

SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

Original Author: Zbigniew Chamski (Thales)
-->
# VPtool Introduction

VPTOOL is a tool for creating and managing Verification Plans.  It supports concurrent editing
at the granularity of Features: each Feature can be locked by a different user.
The lock is persistent and must be explicitly released in order to let another user edit
the information associated with the given Feature.

The user interface of VPTOOL provides a means of entering all information mentioned in the CORE-V
"How to Write a Verification Plan" document available at
https://github.com/openhwgroup/core-v-verif/blob/master/docs/VerifPlans/VerificationPlanning101.md.

When creating new Feature Test descriptions, text fields provide the user with cues about the kind
of information to enter in each field.  All text fields support an "Undo" feature that allows to
revert unwanted changes while editing the text.

The labels and cue texts of VPTOOL are customizable by means of a configuration file so that the
tool can be tailored to the needs of a site, e.g., to use local customary names of verification
concepts.

## Issue Reporting

VPTOOL is in active development and is not fully tested.
If you encounter a problem with VPTOOL, please open an issue on the
[OpenHW Group `core-v-verif` repository](https://github.com/openhwgroup/core-v-verif) (with our thanks!).

## Prerequisites

* Python3: VPTOOL is fully Python3-compliant.  You need a recent version of Python3 with default
  libraries installed, in particular an up-to-date version of `pip3`, the Python3 package installer.
  Use `pip3 install --upgrade pip` to bring you `pip3` up to date.
  If you are in an environment without internet access, download a recent distribution package
  of `pip3` and use local installation features of `pip3` (cf. `pip3 help install`).

* Python TkInter: The Tk interaction package for Python.  It comes pre-packaged for most
  platforms and requires superuser privileges in order to be installed.  On Debian/Ubuntu
  use `sudo apt-get install python3-tk`.  On RedHat-based systems (RedHat/CentOS/Fedora), use
  `sudo dnf install python3-tkinter` or `sudo yum install python3-tkinter`, as appropriate.

* Ruamel YAML: a YAML I/O library for Python with round-trip parse/unparse capabilities.
  Install using `pip3 install --upgrade ruamel.yaml`.

* Pillow: A replacement for the original PIL (Python Image Library).  Install using
  `pip3 install --upgrade pillow`.

* Themed Tk: For a customizable look-and-feel VPTOOL relies on the theme-capable version
  of the Python Tk toolkit interface.  Install using `pip3 install --upgrade ttkthemes`.

## Configuration

[To be completed (lots of work ahead:-D)]

`VPTOOL` can be configured by setting three shell environment variables:

- `PLATFORM_TOP_DIR` shall point to the platform-related directory that contains:
  - the verification database files of the project, stored in YAML format;
  - OPTIONALLY: an administrative directory named `vptool` that contains the project-specific
    `VPTOOL` configuration file `vp_config.py` and the lock files for concurrent
    multi-user editing of the database.
- `PROJECT_NAME` is a free-form string that sets the project name used in the GUI;
- `PROJECT_IDENT` is an alpha-numerical identifier (C-style) that will be used to set unique Verification
  Item tags.

### Python-level configuration

The key configuration information is stored in file `$PLATFORM_TOP_DIR/vptool/vp_config.py`.  This file
contains a series of Python variable assignments which define the operation mode of VPTOOL and the path
to database files.

The key Python variables are:
* `PROJECT_NAME`: a free-form string that identifies the project targeted by the verification plan.
* `PROJECT_IDENT`: an alpha-numerical identifier (C-style) that will be used to generate unique
  Verification Item tags.
* `SAVED_DB_LOCATION`: path to the databases (either a file name, or a directory name).  It is constructed
  from the value of `PLATFORM_TOP_DIR` in `vptool/vp_config.py` so that it can be tailored to any
  organization- or site-specific directory naming conventions.
* `SPLIT_SAVE`: if set to 'True', then verification plan data associated with each Feature is stored
  in separate `VP_IPnnn.pck` files in the directory designated by `SAVED_IP_LOCATION`.
  If `SPLIT_SAVE` is set to `False`, the verification plan data for **ALL** Features will be stored
  in a single file named according to the value of variable `SAVED_IP_LOCATION`.
* `LOCKED_IP_LOCATION': Name of the file holding the locks that control editing access to indivdual
  Features.

## Usage

Once VPTOOL is installed and configured, the tool operates on database files located in the directory
designated by the `SAVED_IP_LOCATION` Python variable, as set inside `vp_config.py`.

The examples below are based on the code preview in current directory.  For convenience, the `VPTOOL`
application and the necessary environment setup (variables, directories, etc.) have been wrapped into a simple
shell script named `vptool-example.sh` which can be invoked from any location.

### Directory structure

- `README.md`:                   this file
- `vptool`:                      the code of `VPTOOL`
- `vptool-example`:              an example of `VPTOOL` configuration with a verification database
  - `runme.sh`:                  a shell script to run `VPTOOL` with the example database
  - `example-database`:          Verification Plan data and `VPTOOL` administrative files for the example
    - `ip_dir`:                  arbitrary subdirectory level (to accommodate site/organization conventions)
      - `core-v`:                another arbitrary subdirectory level (to accommodate, e.g., project architecture)
        - `cva6`:                another arbitrary subdirectory level
          - `locked_ip.pick`:    `VPTOOL` lock file (created upon first `VPTOOL` invocation)
          - `VP_IP000.yml`:      database file of first feature
          - `VP_IP001.yml`:      database file of second feature
          - `...`:               ...

### Basic use

- Start VPTOOL:

    sh vptool-example/runme.sh

  This will load all per-feature Verification Plans present in the `SAVED_DB_LOCATION` variable.
  The corresponding path is `vptool-example/example-database/ip_dir/core-v/cva6/\*.yml`.

  The New and Delete buttons at the bottom of the Feature, Sub-Feature and Verification Item selectors
  are greyed out except for the `New` button of the Feature selector.  This indicates that the user does
  not hold the lock(s) permitting to edit the Feature that may be currently selected.

- Select another Feature to see if you or someone else hold a lock on it:
  - a feature locked by you will have its name colored in green
    (FIXME: achieving proper color change may require clicking on another feature first)
  - a feature locked by someone else will have its background colored in orange

- Lock a feature to enable editing its content:
  - Select a feature in the Feature list by single-clicking on its name
  - At this point you can use either of the following lock toggling methods:
    - In the menu bar click on the `Function` drop-down menu, then select the `Lock/Unlock Feature` entry
    - Press and hold the Ctrl key, then click Button 1 of your mouse on the selected feature

  The name of feature will appear in green and the buttons `New` and `Delete` of the Sub-Feature and
  Feature Test lists will become active.

  To unlock a Feature (release the editing lock that you hold) simply perform the same action as for locking.

- Edit the properties of a feature:
  - Click on a locked Feature entry (name in green) to select the feature to modify
  - Click on the desired Sub-Feature to select it
  - Click on a Feature Test item to select it

  The Item Description information appears in the right-hand pane.  You can edit the text fields and
  change the setting of radio button selectors.

  Changes to drop-down selectors and check buttons take effect immediately.  Changes to text fields
  require a confirmation by pressing the `Save` button.  Unwanted text changes be discarded by pressing
  the `Cancel` button.  Both buttons are only active when the Feature is locked and at least one text
  field was edited.

- Add a new feature, sub-feature, or verification item
  - To add a feature:
    - Click the `New` button under the Feature list
    - Type the name of the new feature
    - Click the `OK` button (or `Cancel` to abandon the action)

    Since database locking is performed on a per-feature basis, a new feature can be added at any time
    (also when all current features are locked by other users).

  - To add a sub-feature to an existing feature:
    - Select and lock the desired feature
    - Click the `New` button under the Sub-Feature list
    - Type the name of the new sub-feature
    - Click the `OK` button (or `Cancel` to abandon the action)

  - To add a new verification item:
    - Select and lock the desired feature
    - Select the desired sub-feature
    - Click the `New` button under the Feature Item list
    - Fill the fields, then click the `Save` button.
