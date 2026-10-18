#include <array>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <string>
#include <sys/wait.h>
#include <utility>

namespace fs = std::filesystem;

std::string quote(const std::string &text)
{
  std::string result = "'";
  for(char c : text)
    result += c == '\'' ? "'\\''" : std::string(1, c);
  return result + "'";
}

std::pair<int, std::string> run(const std::string &command, const fs::path &log)
{
  int status = std::system((command + " > " + quote(log.string()) + " 2>&1").c_str());
  std::ifstream input(log);
  std::ostringstream output;
  output << input.rdbuf();
  int exit_code = status >= 0 && WIFEXITED(status) ? WEXITSTATUS(status) : -1;
  return {exit_code, output.str()};
}

int main(int argc, char **argv)
{
  if(argc != 4)
    return 1;
  const fs::path tools = argv[1];
  const fs::path scratch = argv[2];
  const std::string compiler = quote(argv[3]);
  const std::array<std::pair<std::string, std::string>, 5> cases = {{
    {"explicit", "__CPROVER_assigns(i, value)"},
    {"inferred", ""},
    {"empty", "__CPROVER_assigns()"},
    {"mixed", "__CPROVER_assigns(i, value)"},
    {"omitted", "__CPROVER_assigns(i)"},
  }};
  for(const auto &test : cases)
  {
    const auto &name = test.first;
    const fs::path source = scratch / (name + ".c");
    const fs::path model = scratch / (name + ".gb");
    const fs::path checked = scratch / (name + ".checked.gb");
    const fs::path log = scratch / (name + ".log");
    // C is an input fixture for the instrumenter. The test driver and all
    // verification-result checks are C++, matching the patched implementation.
    std::ofstream fixture(source);
    fixture
      << "void write_next(unsigned *value) { ++*value; }\n"
         "int main(void) { unsigned i = 0, value = 0;\n"
         "for(; i < 3; ++i)\n"
      << test.second
      << "\n__CPROVER_loop_invariant(i <= 3 && value == i)\n{ write_next(&value); }\n"
         "__CPROVER_assert(value == 3, \"loop value\");\n";
    if(name == "mixed")
      fixture
        << "for(i = 0; i < 3; ++i)\n"
           "__CPROVER_loop_invariant(i <= 3 && value == i + 3)\n"
           "{ write_next(&value); }\n"
           "__CPROVER_assert(value == 6, \"inferred second loop value\");\n";
    fixture << "return 0; }\n";
    fixture.close();
    const std::array<std::string, 2> preparation = {{
      compiler + " " + quote(source.string()) + " -o " + quote(model.string()),
      quote((tools / "goto-instrument").string()) +
        " --dfcc main --apply-loop-contracts --loop-contracts-no-unwind " +
        quote(model.string()) + " " + quote(checked.string()),
    }};
    for(const auto &command : preparation)
    {
      const auto result = run(command, log);
      if(result.first != 0)
      {
        std::cerr << result.second;
        return 1;
      }
    }
    const auto result = run(
      quote((tools / "cbmc").string()) + " " + quote(checked.string()) +
        " --unwind 5 --unwinding-assertions", log);
    const bool omitted = name == "omitted";
    if(result.first != (omitted ? 10 : 0) ||
       (omitted && !std::regex_search(result.second, std::regex("assignable[^\n]*FAILURE"))))
    {
      std::cerr << name << ": unexpected result\n" << result.second;
      return 1;
    }
    std::cout << "loop assigns " << name << ": expected verification result confirmed\n";
  }
  return 0;
}
