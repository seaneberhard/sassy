from tqdm.notebook import tqdm

def verbose_iter(iterator, condition, message):
    if condition:
        print(message)
        return tqdm(iterator)
    return iterator
