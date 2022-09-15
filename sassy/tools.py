from tqdm.notebook import tqdm

def verbose_iter(iterator, condition, message, total=None):
    if condition:
        print(message)
        return tqdm(iterator, total=total)
    return iterator
