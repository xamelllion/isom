# Отчёт: реализация и сравнение алгоритмов проверки изоморфизма гиперграфов отношений

Отчёт сделан на основе шаблона
[spbu-se/matmex-diploma-template](https://github.com/spbu-se/matmex-diploma-template)
(класс `matmex-diploma-custom.cls`, стиль библиографии `ugost2008ls.bst`).

## Структура

| Файл | Содержание |
|---|---|
| `report.tex` | главный файл |
| `title.tex` | данные титульного листа (поля с `TODO` заполнить) |
| `000_intro.tex` | введение |
| `010_task.tex` | постановка задачи |
| `020_related.tex` | обзор: определения, ISOM-1, ISOM-n, пример работы, существующие подходы |
| `030_solution.tex` | реализация на Python и C++, средства сравнения |
| `040_experiment.tex` | эксперимент: условия, наборы задач, результаты, графики |
| `050_conclusion.tex` | заключение |
| `report.bib` | список литературы |
| `data/prepare.py` | строит данные для таблиц и графиков из `../bench` |

Графики строятся pgfplots прямо из CSV в `data/`, отдельных картинок нет.

## Сборка

```sh
python3 ../compare.py   # из корня проекта: замеры → ../bench/results.csv, ../bench/full_run.log
make                    # пересчитывает data/ и собирает report.pdf (LuaLaTeX)
```

`make` сам вызывает `data/prepare.py`, если результаты замеров новее данных отчёта.
По умолчанию используется LuaLaTeX: он находит шрифты CMU в дереве TeX Live.
Для XeLaTeX (`make ENGINE=xelatex`) шрифты должны быть установлены в систему
(`sudo apt install fonts-cmu`).

Пакет `minted` подключается классом шаблона, но в отчёте не используется:
листинги набраны пакетом `listings`, поэтому `latexminted` не нужен.
