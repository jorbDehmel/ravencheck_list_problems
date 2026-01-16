'''
Iterates through elements in ./problems and copies them to
correspondingly-named elements in ./src
'''

import os
from typing import List

src_dir: str = './problems'
dst_dir: str = './src'

filepaths: List[str] = []
for path, folders, files in os.walk(src_dir):
  # Iterate over files
  for filename in files:
    filepaths.append(os.path.join(path, filename))

filepaths.sort()

i: int = 1
for src_file_path in filepaths:
  tgt_file_path = os.path.join(dst_dir, f'p{i}.rs')

  with open(tgt_file_path, 'w') as tgt:
    src_txt = ''
    with open(src_file_path, 'r') as f:
      src_txt = f.read()

    tgt.write(f'// {src_file_path}\n\n')
    tgt.write('/*\n')
    tgt.write(src_txt)
    tgt.write('*/\n\n')

    tgt.write(
      '#[ravencheck::check_module]\n' +
      '#[allow(dead_code)]\n' +
      'mod ' + f'p{i}' + ' {\n' +
      '}\n'
    )

    print(f'{src_file_path} | {tgt_file_path}')

  i += 1
