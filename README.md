# Checking the model in VS Code

Before running model check disable deadlock detection and set number of workers to 8 in `settings.json`:

```
{
    "tlaplus.tlc.modelChecker.options": "-deadlock -workers 8"
}
```
