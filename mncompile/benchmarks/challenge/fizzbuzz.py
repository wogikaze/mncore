def kernel():
    def word(i):
        if i % 15 == 0:
            return "FizzBuzz"
        if i % 3 == 0:
            return "Fizz"
        if i % 5 == 0:
            return "Buzz"
        return str(i)

    return "\n".join(word(i) for i in range(1, 6335))
