A Lean 4 formalization of [Helena 
Rasiowa's](https://en.wikipedia.org/wiki/Helena_Rasiowa) "Introduction to Modern 
Mathematics" (Polish original title: "Wstęp do matematyki współczesnej")

This is an educational project emphasizing detailed explanations to the 
"Explain like I'm five" level. Minimal knowledge is assumed. If that's not 
what you see here, please open an issue.

Do not expect too much as it only covers first 4 pages out of 290 in the book.

See [the series of blog posts about the project so 
far](https://filip.lajszczak.dev/lean-4-with-a-math-textbook---part-0---introduction.html).

## Structure

- **Chapter I**: Set Algebra (`Rasiowa.Basic`)
    - §1: Basic set concepts, subset relations, basic properties
    - §2-8: Set operations, complements, Boolean algebras (might be added later)

## Installation

This project requires Lean 4. See [Lean's installation 
instructions](https://lean-lang.org/install/).

```bash
git clone https://github.com/filiplajszczak/rasiowa-formalization.git
cd rasiowa-formalization
lake build
```

## Usage

```lean
import Rasiowa.Basic  -- All of Chapter I
-- or
import Rasiowa.Section1  -- Just basic set theory
```

## Contributing

Contributions are welcome, especially those that enhance clarity or correctness.
Verbosity is preferred over conciseness. Step-by-step approaches are 
encouraged. Feel free to open issues or pull requests. 

## References

- Rasiowa, Helena. (1968). *Wstęp do matematyki współczesnej*.
Warszawa: Państwowe Wydawnictwo Naukowe. (Multiple reprints)
- Rasiowa, Helena. (1973). *Introduction to modern mathematics*. North-Holland
Publishing Company. (O. Wojtasiewicz, Trans.)