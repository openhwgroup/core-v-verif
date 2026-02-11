coverage attr  -name TESTNAME -value [format "%s" $::env(TEST_COV)$::env(TEST_CFG_FILE_COV)__$::env(TEST_CONFIG_COV)__$::env(TEST_SEED_COV)]
coverage attr  -test $::env(TEST_COV)_$::env(TEST_CFG_FILE_COV)__$::env(TEST_CONFIG_COV)__$::env(TEST_SEED_COV)
coverage save -onexit $::env(TEST_COV)$::env(TEST_CFG_FILE_COV).ucdb
