from colorama import Fore, Back, Style

from utils import Programs



from semantic.SemanticHelper import getSemanticSolver


def main():
    directory = "dev_tools/temp/GEN_a6_r8/"
    tests_amount = 500
    passed = 0
    failed = 0
    failed_test_cases = list()

    for i in range(tests_amount):
        i = 30
        concrete_file = directory+"concrete/concrete_"+str(i)+".af"
        abstract_file = directory+"abstract/abstract_"+str(i)+".af"

        Programs.clearSolver()

        ret = Programs.checkTheory(concrete_file=concrete_file, abstract_file=abstract_file, semantics="ST")

        if ret == "ConcretizedSpurious":
            print(f"Test {i:3} [" + Fore.YELLOW + Style.BRIGHT + "SKIPPED" + Fore.WHITE + Style.RESET_ALL + "]")

        elif ret == "DirectFaithful":
            print(f"Test {i:3} [" + Fore.YELLOW + Style.BRIGHT + "SKIPPED" + Fore.WHITE + Style.RESET_ALL + "]")

        elif ret == True:
            passed += 1
            print(f"Test {i:3} [" + Fore.GREEN + Style.BRIGHT + "PASSED " + Fore.WHITE + Style.RESET_ALL + "]")
        elif ret == False:
            failed += 1
            print(f"Test {i:3} [" + Fore.RED + Style.BRIGHT + "FAILED " + Fore.WHITE + Style.RESET_ALL + "]")
            failed_test_cases.append((concrete_file, abstract_file))
        exit()
    print("-------------------------------------------------")
    print(f"Amount: {Fore.BLUE + Style.BRIGHT}{tests_amount}{Style.RESET_ALL}")
    print(f"Passed: {Fore.GREEN + Style.BRIGHT}{passed}{Style.RESET_ALL}")
    print(f"Failed: {Fore.RED + Style.BRIGHT}{failed}{Style.RESET_ALL}")
    print("-------------------------------------------------")
    print(f"Failed Testcases:")
    for i in failed_test_cases:
        print("  ", i)
    exit()

if __name__ == "__main__":
    main()