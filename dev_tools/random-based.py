import sys
import random
sys.path.append('../')
from utils import Visualizer
from utils import Parser

out_path = "~/Desktop/argumentation-framework-clustering/input/experiment/random-based/"

def main():
    if len(sys.argv) != 4:
        print("usage: python3 random-based.py <af_amount> <arg_amount> <p>")
        exit()

    af_amount = int(sys.argv[1])
    arg_amount = int(sys.argv[2])
    probability = float(sys.argv[3])
    file_name = f"concrete.af"

    for i in range(af_amount):

        with open(f"{out_path}{file_name}", "w") as f:
            f.write(f"p af {arg_amount}\n")
            f.write("# Generated with random-based.py script.\n")
            f.write(f"# Amount arguments: {arg_amount}\n")
            f.write(f"# Probability: {probability}\n")

            for a in range(arg_amount):
                for b in range(arg_amount):
                    rand = random.random()
                    if rand <= probability:
                        f.write(f"{a} {b}\n")

        print("successfully generated.")



if __name__ == "__main__":
    main()