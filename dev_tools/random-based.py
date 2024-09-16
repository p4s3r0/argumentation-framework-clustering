import sys
import random

out_path = "out"

def main():
    if len(sys.argv) != 4:
        print("usage: python3 random-based.py <arg_amount> <p> (<af_amount>)")
        exit()

    af_amount = int(sys.argv[3])
    arg_amount = int(sys.argv[1])
    probability = float(sys.argv[2])
    file_name = f"concrete"

    attack_list = list()

    for i in range(af_amount):
        with open(f"{out_path}/{file_name}_{i}.af", "w") as f:
            f.write(f"p af {arg_amount}\n")
            f.write(f"# Generated with random-based.py script.\n")
            f.write(f"# Amount arguments: {arg_amount}\n")
            f.write(f"# Probability: {probability}\n")

            for a in range(arg_amount):
                for b in range(arg_amount):
                    rand = random.random()
                    if rand <= probability:
                        if a not in attack_list:
                            attack_list.append(a)
                        if b not in attack_list:
                            attack_list.append(b)
                        f.write(f"{a} {b}\n")


            if len(attack_list) < arg_amount:
                f.write("--attackless--\n")
                for i in range(arg_amount):
                    if i not in attack_list:
                        f.write(f"{i}\n")

    print("successfully generated.")



if __name__ == "__main__":
    main()
