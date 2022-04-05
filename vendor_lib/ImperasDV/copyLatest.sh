#!/bin/bash

# remove folders so we dont retain any removed files
rm -rdf ImpPublic
rm -rdf ImpProprietary

# re-create folder structure
mkdir -p ImpPublic/include/host/rvvi
mkdir -p ImpPublic/source/host/rvvi
mkdir -p ImpProprietary/source/host/rvvi
mkdir -p lib/Linux64/ImperasLib/imperas.com/verification/riscv/1.0
mkdir -p lib/Linux64/ImperasLib/riscv.ovpworld.org/processor/riscv/1.0
mkdir -p lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/intercept/extension/1.0
mkdir -p lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/processor/riscv/1.0

# copy over from Imperas sandbox
cp $IMPERAS_HOME/ImpPublic/include/host/rvvi/* ImpPublic/include/host/rvvi
cp $IMPERAS_HOME/ImpPublic/source/host/rvvi/* ImpPublic/source/host/rvvi
cp $IMPERAS_HOME/ImpProprietary/source/host/rvvi/* ImpProprietary/source/host/rvvi

cp $IMPERAS_HOME/lib/Linux64/ImperasLib/imperas.com/verification/riscv/1.0/model.so \
                 lib/Linux64/ImperasLib/imperas.com/verification/riscv/1.0/model.so
cp $IMPERAS_HOME/lib/Linux64/ImperasLib/riscv.ovpworld.org/processor/riscv/1.0/model.so \
                 lib/Linux64/ImperasLib/riscv.ovpworld.org/processor/riscv/1.0/model.so
cp $IMPERAS_HOME/lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/intercept/extension/1.0/model.so \
                 lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/intercept/extension/1.0/model.so
cp $IMPERAS_HOME/lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/processor/riscv/1.0/model.so \
                 lib/Linux64/ImperasLib/openhwgroup.ovpworld.org/processor/riscv/1.0/model.so

