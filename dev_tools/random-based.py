import sys
import random
sys.path.append('../')
from utils import Visualizer
from utils import Parser



def main():
    if len(sys.argv) != 3:
        print("usage: python3 random-based.py <arg_amount> <p>")
        exit()

    arg_amount = int(sys.argv[1])
    probability = float(sys.argv[2])
    file_name = f"GEN-random-a{arg_amount}-p{str(probability).replace('.', '')}.af"


    with open(file_name, "w") as f:
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

    parser = Parser.Parser()
    parser.parseFile(file_name)
    Visualizer.show(parser.arguments)



if __name__ == "__main__":
    main()