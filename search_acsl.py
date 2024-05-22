# -*- coding: utf-8 -*-

from pyparsing import Word, alphas, alphanums, Literal, Forward, Group, ZeroOrMore, OneOrMore, Suppress
import os
import re
import sys
import datetime
from copy import deepcopy

acsl_dir = None


def find_logic(input_string):
    word = Word('*' + alphas + '_')
    number = Word(alphanums)
    operator = Literal('<=') | Literal('>=') | Literal('==') | Literal('%') | Literal('=') | Literal('!=') | Literal(
        '+') | Literal(
        '-') | Literal('..') | Literal('.') | Literal(
        '/') | Literal(';') | Literal('&&') | Literal('||') | Literal(',') | Literal('<') | Literal('>') | Literal(
        '==>') | Literal(':')
    at = Suppress(Literal('at'))
    new = Literal('\n')
    comma = Literal(',')
    lparen = Literal('(')
    rparen = Literal(')')
    backslash = Suppress("\\")
    lbracket = Literal('[')
    rbracket = Literal(']')
    lrracket = Literal('{')
    rrracket = Literal('}')
    not_op = Literal('NOT')
    exists_op = Literal('EXISTS')

    result = Literal('result')
    assigns = Literal('assigns')
    empty = Literal('empty')

    expression = Forward()
    expression << (word | number | operator | lparen | rparen | backslash | lbracket | rbracket | lrracket | rrracket | result | assigns | empty)
    expression = Group(expression)

    expression.setParseAction(handle_at)

    keyword_acsl = ['predicate', 'logic', 'requires', 'behavior', 'assumes', 'ensures', 'complete', 'disjoint',
                    '\forall', '\exists', 'ull']
    types = ['int', 'float', 'double', 'boolean']
    parsed = OneOrMore(expression).parseString(input_string)
    parsed_list = [str(token) for token in parsed]
    result = [item.strip("[]'") for item in parsed_list]

    # Фильтрация пустых строк (пустых подмассивов)
    result = [item for item in result if item]

    # Преобразование списка в кортеж
    tuple_result = tuple(result)
    acsl_sections = {}
    current_section = None
    index_equal_sign = tuple_result.index('=')
    filtered_array = tuple_result[:2] + tuple_result[index_equal_sign:]
    for token in filtered_array:
        if token in keyword_acsl:
            current_section = token
            acsl_sections[current_section] = []
        elif current_section:
            if token.isalpha() and len(token) == 1 or token in types:
                pass
            else:
                acsl_sections[current_section].append(token)
    for section, tokens in acsl_sections.items():
        continue
    return tokens


def handle_at(t):
    if len(t) == 3:
        return ['\\at(' + t[1] + ')']
    else:
        return t

def log_changes(log_file_path, logline_1, logline_2, logline_3, filepath):
    # Открываем файл лога для записи
    with open("./log.txt", "a") as log_file:
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_file.write(logline_1)
        log_file.write(logline_2)
        log_file.write(logline_3)
        log_file.write("Время нахождения: {}\n\n".format(timestamp))



def find_pattern(item):
    try:
        func_name = re.findall(r'\b\w+(?=\()', item)
        func_name_2 = re.findall(r"\((\w+)", item)
        l_true = []
        opperand = []
        mini = ''
        params = deepcopy(func_name_2)
        removed = 0
        if func_name != []:
            for count, i in enumerate(func_name):
                if not mini:
                    mini = i
                else:
                    if i != func_name_2[count - 1]:
                        l_true.append(mini + '(')
                        mini = i
                    else:
                        mini += '(' + i
                        params.pop(count - 1 - removed)
                        removed += 1
            else:
                l_true.append(mini + '(')
        # Обработка логических операндов
        logical_operands = ['&&', '||', '==>', '<==>', '!', '\\true', '\\false']
        for operand in logical_operands:
            while operand in item:
                index = item.index(operand)
                l_true.insert(index, operand)
                item = item[:index] + ' ' + item[index + len(operand):]
    except:
        l_true = None
        params = None
        pass
    return l_true, params


def func_var(key, func_name, params):
    # print(params)
    try:
        function_indices = [key.index(f) for f in func_name]
        index_param_dict = {index: param for index, param in enumerate(params)}
        sorted_params = [index_param_dict[index] for index in function_indices]
        sorted_params = list(dict.fromkeys(sorted_params))
        if len(sorted_params) == 1:
            value = ''.join(sorted_params)
        else:
            value = ', '.join(sorted_params)
        # print(value)
        return value
    except:
        pass


# функция для поиска существующих предикатов в файла проекта
def search_acsl(filenames, dictionary):
    # проходим по всем файлам в указанной директории и ее поддиректориях
    for filename in filenames:
        filepath = os.path.join(filename)
        multiline_string = ""
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()
            lines = content.split('\n')
        # читаем содержимое файла построчно
        for num, line in enumerate(lines, 1):
            # ищем ключевые слова requires, ensures и logic
            stripline = line.strip()
            if stripline.startswith("requires") and not stripline.endswith(";"):
                multiline_string += stripline
            elif multiline_string:
                multiline_string += stripline
                if not stripline.endswith(";"):
                    continue
                else:
                    line = multiline_string
                    search_requires(filepath, num - 1, line, dictionary)
                    multiline_string = ""
            else:
                search_requires(filepath, num, line, dictionary)


def search_requires(filepath, num, line, dictionary):
    for keyword in ["requires"]:
        pattern = r'{}\s+(.*?)\s*;'.format(keyword)
        # извлекаем подстроку, соответствующую регулярному выражению
        matches = re.findall(pattern, line)
        for match in matches:
            sort = re.findall(r'\b\w+(?=\()', match)
            # извлекаем аргумент функции
            perem = re.search(r"\((\w+)", match)
            # print(perem)
            if not perem:
                perem = re.findall(r"\b[a-zA-Z]\w*\b", match)
                if len(perem) > 1:
                    perem_str = ', '.join(perem)
            if match:
                # извлекаем имя функции
                if not sort:
                    string = "requires logic =" + match
                    logicmatch = find_logic(string)
                    func_name = tuple(logicmatch[1:])
                    params = ""
                else:
                    func_name, params = find_pattern(match)
                    if not func_name:
                        try:
                            func_name = re.findall(r'(\w+)\s*([!=<>]+)\s*(\w+)', match)
                            func_name = func_name[0]
                        except:
                            pass
                # ищем, есть ли найденный кортеж в словаре ранее обьявленных конструкций
                for key in dictionary.keys():
                    if sorted(key) == sorted(tuple(func_name)):
                        # print(f"Найден кортеж: {key}")
                        # print(f"Соответствующее значение: {dictionary[key]}")
                        value = func_var(key, func_name, params)
                        # получаем название существующей конструкции из словаря
                        old_key = key
                        key = tuple(sorted(func_name))
                        # получаем номер символа
                        char_num = line.find(keyword)
                        prefix = line[:char_num]
                        logline_1 = "Может быть использован предикат '{}'".format(dictionary[old_key]) + "\n"
                        logline_2 = "--> {}:{}:{}\n |\n{}|{}".format(filepath, num, char_num, num, line.rstrip()) + "\n"
                        logline_3 = " |" + " " * (char_num) + " " * (len(keyword)) + "^" * (
                                len(line.rstrip()) - len(" " * (char_num)) - len(keyword)) + "\n"
                        print(logline_1 + logline_2 + logline_3)
                        log_changes("{}\\log.txt".format(path), logline_1, logline_2, logline_3, filepath)
                        # запрашиваем подтверждение замены строки
                        # confirm = input("Подтверждение операции: (y/n): ")
                        # if confirm.lower() == "y":
                        #     replacement = dictionary[key]
                        #
                        #     new_line = f'{prefix} {keyword} {replacement}({value});'
                        #     lines[num - 1] = new_line
                        #     new_content = '\n'.join(lines)
                        #     # нзаписываем измененное содержимое файла
                        #     with open(filepath, 'w') as f:
                        #         f.write(new_content)
                        #         print(f'Выполенена замена в файле: {os.path.join(filename)}')
                        #     log_changes(f'{path}\\log.txt', line, new_line, filepath)
                        # else:
                        #     print("Замена отменена.")


# функция для поиска существущих acsl конструкций
def get_acsl(directory):
    with open(os.path.join(directory), "r") as f:
        text = f.read()
    func_dict = {}
    all_matches = []
    for keyword in ["predicate"]:
        # ищем объявления функций с помощью регулярного выражения
        matches = re.findall(r'{}\s+(\w+)\((.*?)\)\s*=\s*(.*?);'.format(keyword), text, re.DOTALL)
        all_matches.extend(matches)
        # ищем объявления функций с помощью регулярного выражения
        for match in all_matches:
            sort = re.findall(r'\b\w+(?=\()', match[2])
            if sort:
                l_true, params = find_pattern(match[2])
                print(match[0], " : ", l_true)
                if l_true:
                    func_dict[tuple(l_true)] = match[0]
            else:
                combined_string = "predicate " + match[0] + '( ' + match[1] + ' ) ' + ' = ' + ' ' + match[2]
                logicmatch = find_logic(combined_string)
                func_dict[tuple(logicmatch[2:])] = logicmatch[0]
        # exprs = find_logic(text)
        # exprs = re.findall(r'(\w+)\s*([!=<>]+)\s*(\w+)', text)
        # for expr in exprs:
        #     # добавляем выражение в словарь func_dict
        #     func_dict[tuple([expr[1]])] = match[0]
    # print(func_dict)
    search_acsl(filenames, func_dict)


# функция для получения списков файла проекта, которые необходимо проверить
def get_filenames(cur):
    filenames = []
    if len(os.listdir(cur)) == 0:
        print("Директория пустая")
    else:
        for dr in os.listdir(cur):
            abs_path = os.path.join(cur, dr)
            # проверяем, что мы получили, папку или файл
            if os.path.isdir(abs_path):
                # если мы нашли папку, то рекурсивно вызываем функцию для прохода по ней
                filenames += get_filenames(abs_path)
            else:
                # проверяем, что файл имеет расширение .c или .h
                if abs_path.endswith('.c') or abs_path.endswith('.h'):
                    # если название файла не acsl.c, добавляем его путь в список
                    if os.path.basename(abs_path) != 'acsl.c':
                        filenames.append(abs_path)
                    # если название файла acsl.c, добавляем его путь в отдельную переменную
                    if os.path.basename(abs_path) == 'acsl.c':
                        global acsl_dir
                        acsl_dir = abs_path
        if acsl_dir == None:
            print("Не найден файл acsl.c")
        return filenames


if __name__ == '__main__':
    # path = 'C:\\folder'
    try:
        if len(sys.argv) != 2:
            print("Usage: {} path".format(sys.argv[0]))
            sys.exit(1)
        path = sys.argv[1]
        # path = 'C:\\folder\\test\\itog'
        filenames = get_filenames(path)
        get_acsl(acsl_dir)
    except:
        print("")
