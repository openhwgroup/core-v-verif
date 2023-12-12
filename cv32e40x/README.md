The verification specifics for core cv32e40x are in a separate repository, (https://github.com/openhwgroup/cv32e40x-dv). To download the repository, do the following:

1) Make sure your pwd end folder is core-v-verif:
pwd = (...)/core-v-verif
2) Run the clonetb script from the bin folder with the x agrument as shown:
./bin/clonetb -x

The bin/clonetb script populates the cv32e40x folder with the content of cv32e40x-dv on a stable hash. Use git status to check the hash.
