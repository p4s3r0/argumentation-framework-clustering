import sys
import random

out_path = "../input/experiment/random-based/concrete"

def main():
    if len(sys.argv) != 4:
        print("usage: python3 random-based.py <arg_amount> <p> (<af_amount>)")
        exit()

    af_amount = int(sys.argv[3])
    arg_amount = int(sys.argv[1])
    probability = float(sys.argv[2])
    file_name = f"args-{arg_amount}-p-{int(probability*100)}"

    attack_list = list()

    for i in range(af_amount):
        with open(f"{out_path}/{file_name}-i-{i}.af", "w") as f:
            f.write(f"p af {arg_amount}\n")
            f.write(f"# approach: random-based\n")
            f.write(f"# arg_amount: {arg_amount}\n")
            f.write(f"# p: {probability}\n")

            write_cache = list()
            for a in range(arg_amount):
                for b in range(arg_amount):
                    rand = random.random()
                    if rand <= probability:
                        if a not in attack_list:
                            attack_list.append(a)
                        if b not in attack_list:
                            attack_list.append(b)
                        write_cache.append(f"{a} {b}\n")

            f.write(f"# att_amount: {len(write_cache)}\n")

            for w in write_cache:
                f.write(w)

            if len(attack_list) < arg_amount:
                f.write("--attackless--\n")
                for i in range(arg_amount):
                    if i not in attack_list:
                        f.write(f"{i}\n")


    print(f"Generated {af_amount} concrete AFs.")



if __name__ == "__main__":
    main()
