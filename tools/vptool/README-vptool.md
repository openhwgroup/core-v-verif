# VPtool Introduction

NOTE: This document is by no means exhaustive and is built incrementally from user experience.
Therefore, it may contain mistakes and/or it may suggest non-optimal ways of dealing with VPTOOL.

`VPTOOL` is a tool for creating and managing Verification Plans.  It supports concurrent editing
at the granularity of Features: each Feature can be locked by a different user.
The lock is persistent and must be explicitly released in order to let another user edit
the information associated with the given Feature.

The user interface of `VPTOOL` provides a means of entering all information mentioned in the CORE-V
"How to Write a Verification Plan" document available at
https://github.com/openhwgroup/core-v-verif/blob/master/docs/VerifPlans/VerificationPlanning101.md.

When creating new Feature Test descriptions, text fields provide the user with cues about the kind
of information to enter in each field.  All text fields support an "Undo" feature that allows to
revert unwanted changes while editing the text.

The labels and cue texts of `VPTOOL` are customizable by means of a configuration file so that the
tool can be tailored to the needs of a site, e.g., to use local customary names of verification
concepts.

## Prerequisites

* Python3: `VPTOOL` is fully Python3-compliant.  You need a recent version of Python3 with default
  libraries installed, in particular an up-to-date version of `pip3`, the Python3 package installer.
  Use `pip3 install --upgrade pip` to bring you `pip3` up to date.
  If you are in an environment without internet access, download a recent distribution package
  of `pip3` and use local installation features of `pip3` (cf. 'pip3 help install').

* `PyYAML`: a YAML I/O library for Python.  Install using `pip3 install --upgrade pyyaml`.

* `Pillow`: A replacement for the original `PIL` (Python Image Library).  Install using
  `pip3 install --upgrade pillow`.

* Themed Tk: For a customizable look-and-feel `VPTOOL` relies on the theme-capable version
  of the Python Tk toolkit interface.  Install using `pip3 install --upgrade ttkthemes`.

## Configuration

[To be completed (lots of work ahead:-D)]

The key configuration information is stored at the location corresponding to the file *or symbolic link*
'vp_config.py' in `VPTOOL` source directory.  The actual file contains a series of Python variable
assignments which define the operation mode of `VPTOOL` and the paths to databases, lock files, etc.

The Python code queries the presence and the value of shell environment variable `PLATFORM_TOP_DIR`.
This variable must be defined before launching `VPTOOL`.  It shall point to the top-level directory
of the platform-related tree.

NOTE: it is considered good practice to set `PLATFORM_TOP_DIR` to the top-level directory
of a verification project and to invoke `VPTOOL` from that directory.  This allows to use paths
*inside* `$PLATFORM_TOP_DIR` to store and access Verification Plan data, thus diminishing the risk
of inconsistencies between actual IP being verified and the associated Verification
Plan.  For this reason, `VPTOOL` will issue a warning if it is not invoked from '$PLATFORM_TOP_DIR'
(the code of `VPTOOL` itself can be installed anywhere, what counts is the current working dir.)
  
The key Python variables are:
* `SAVED_DB_LOCATION`: path to the databases (either a file name, or a directory name)
* `PROJECT NAME`: set from shell variable of the same name, or empty if no such variable was set.
* `SPLIT_SAVE': if set to `True`, then verification plan data associated with each Feature is stored
  in separate `VP_IPnnn.pck` files in the directory designated by `SAVED_IP_LOCATION`.
  If 'SPLIT_SAVE' is set to `False`, the verification plan data for **ALL** Features will be stored
  in a single file named according to the value of variable `SAVED_IP_LOCATION`.
* `LOCKED_IP_LOCATION`: Name of the file holding the locks that control editing access to indivdual
  Features.

## Usage

Once `VPTOOL` is installed and configured, the tool operates on database files located in the directory
designated by the `SAVED_IP_LOCATION` Python variable, as set inside `vp_config.py`.

The examples below are based on the code preview in current directory.  For convenience, the VPTOOL application
and the necessary environment setup (variables, directories, etc.) have been wrapped into a simple
shell script named `vptool-example.sh` which can be invoked from any location.

### Directory structure

- vptool-example.sh         toplevel example script
- vplan_database            Verification Plan data and administrative files
  - vplan_database/ip_dir   location of Verification Plan data (one file per feature)
  - vplan_database/admin    administrative files - currently only the list of locks on individual feature files
- vptool                    the code of `VPTOOL`

### Basic use

- Start `VPTOOL`:

    sh vptool-example.sh

  This will load all per-feature Verification Plans present in the `SAVED_DB_LOCATION` variable.
  The corresponding path is `vplan_database/ip_dir/*.pck` as defined in the configuration file
  `vptool/vp_config.py`.

  The New and Delete buttons at the bottom of the Feature, Sub-Feature and Verification Item selectors
  are greyed out except for the `New` button of the Feature selector.  This indicates that the user does
  not hold the lock(s) permitting to edit the Feature that is currently selected.

- Select another Feature to see if you or someone else hold a lock on it:
  - a feature locked by you will have its name colored in green
    (FIXME: achieving proper color change may require clicking on the (un)locked feature first)
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

  The `Item Description` information appears in the right-hand pane.  You can edit the text fields and
  change the setting of drop-down and checkbutton selectors.
  
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
