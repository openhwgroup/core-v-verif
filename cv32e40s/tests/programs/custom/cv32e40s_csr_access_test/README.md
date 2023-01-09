CSR access test for (a practical subset of) implemented CSRs (i.e. not for the _whole_ 4096 range).

Generated from "riscv-dv"'s `scripts/gen_csr_test.py`, via core-v-verif's
`bin/gen_csr_access_test.py`, using the csr yaml definition in the core's repo.

From top-level:
```
python3 ./bin/gen_csr_access_test.py  \
  --core=cv32e40s     \
  --clint_enable      \
  --i_base_enable     \
  --m_ext_enable      \
  --umode_enable      \
  --zc_enable         \
  --mhpmcounter_num 0 \
  --num_triggers    0 \
  --pmp_num_regions 0 \
  --output=./cv32e40s/tests/programs/custom/cv32e40s_csr_access_test/ \
  --m4
```
The above options were the most applicable at the time of writing and are subject to change.
Note that excluded options and parameters need targeted separate testing.

[comment]: # (TODO:silabs-robin Regen with "--xsecure_enable" etc after iss bugfix and rtl progression)
