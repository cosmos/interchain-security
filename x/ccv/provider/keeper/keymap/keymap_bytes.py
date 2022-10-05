num_chains = 20
num_validators = 175
key_bytes = 64


def compute_usage():

    # must store 4 keys per validator
    fixed = num_chains * num_validators * 4 * key_bytes

    # in a very pessimistic case, we must store 10
    # old keys, for each validator
    pessimism_factor = 10 * key_bytes
    return fixed * pessimism_factor


bytes = compute_usage()
kibiytes = bytes / 1024
mibibytes = kibiytes / 1024
print(mibibytes)
