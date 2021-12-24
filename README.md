# FicroKanSharp

A microKanren implementation in F#.

# Development tips

There are pull request checks on this repo, enforcing [Fantomas](https://github.com/fsprojects/fantomas/)-compliant formatting.
After checking out the repo, you may wish to add a pre-push hook to ensure locally that formatting is complete, rather than having to wait for the CI checks to tell you that you haven't formatted your code.
Consider performing the following command to set this up in the repo:
```bash
git config core.hooksPath hooks/
```
Before your first push (but only once), you will need to install the [.NET local tools](https://docs.microsoft.com/en-us/dotnet/core/tools/local-tools-how-to-use) which form part of the pre-push hook:
```bash
dotnet tool restore
```

