import sys
'''
Creates a Clustered AF from the input file. The Cluster Contains 
<X> Singletons, where <X> is defined as command line argument.
the input format is the following:
input format: python3 RandomClusterScript.py <filename> <cluster_size>
'''


def readFile(filename: str):
    arg_amount= 0
    attacks=list()

    with open(filename, "r") as f: 
        arg_amount = int(f.readline().split()[2])
        for attack in f:
            if len(attack.split()) <= 0 or attack.split()[0] == '#':
                continue
            
            if len(attack.split()) != 2:
                print("ERROR", attack)

            if attack.split() not in attacks:
                attacks.append(attack.split())
    return arg_amount, attacks



def clusterAF(attacks: list, arg_amount: int, cluster_size: int):
    clustered_attacks = list()

    for attack in attacks:
        attacker = attack[0]
        defender = attack[1]

        if int(attack[0]) <= cluster_size:
            attacker = arg_amount + 10

        if int(attack[1]) <= cluster_size:
            defender = arg_amount + 10

        if [attacker, defender] not in clustered_attacks:
            clustered_attacks.append([attacker, defender])
    return clustered_attacks



def generateFile(C_AF: list, inp_file: str, clustered_argument_amount: int, arg_amount: int):
    with open(f"{inp_file[:-6]}_c{clustered_argument_amount}.af", "w") as f:
        f.write(f"p af {arg_amount - clustered_argument_amount + 1}\n")
        f.write("# Clustered with Script\n")
        for attack in C_AF:
            f.write(f"{attack[0]} {attack[1]}\n")

        f.write("--cluster--\n")
        f.write(f"{arg_amount + 10} <- ")
        for i in range(1, clustered_argument_amount + 1):
            f.write(f"{i} ")



def main():
    print("input format: <filename> <cluster_size>")
    cluster_size = int(sys.argv[2])
    filename=sys.argv[1]
    arg_amount, attacks = readFile(filename)
    if int(cluster_size) > int(arg_amount):
        print("ERROR less arguments than cluster size")

    C_AF = clusterAF(attacks, arg_amount, cluster_size)
    generateFile(C_AF, filename, cluster_size, arg_amount)
    print("Generated new File Successful!")



if __name__ == "__main__":
    main()