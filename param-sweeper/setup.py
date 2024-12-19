from setuptools import setup, find_packages

setup(
    name="param-sweeper",
    version="0.1.0",
    packages=find_packages(),
    install_requires=[
        "numpy",
        "pandas",
        "matplotlib",
        "toml",
        "tqdm",
    ],
    entry_points={
        'console_scripts': [
            'run-sweep=run_sweep:main',
        ],
    },
) 