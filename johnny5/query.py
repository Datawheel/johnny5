import subprocess
import json
import requests

from bs4 import BeautifulSoup
from collections import defaultdict
from itertools import chain

import urllib

try:
	urlencode = urllib.urlencode
except:
	urlencode = urllib.parse.urlencode


def _isiter(obj):
	"""
	Returns True if the object is an iterable, excluding strings.
	"""
	if isinstance(obj, str):
		return False
	else:
		try:
			obj[0]
			return True
		except:
			return False


def _rget(url):
	""" Function used to track the requests that are performed. """
	return requests.get(url, headers={'User-Agent': 'Mozilla/4.0 (compatible; MSIE 6.0; Windows 98)'}).json()
	# p = subprocess.Popen(['curl', url], stdout=subprocess.PIPE)
	# r = p.communicate()[0].decode("utf-8")
	# return json.loads(r)


def _isnum(n):
	""" Returns True if n is a number. """
	try:
		nn = n+1
		return True
	except:
		return False


def _string(val):
	""" If val is a number, it returns the string version of the number, otherwise it returns val. """
	if _isnum(val):
		return str(val)
	else:
		return val


def _join_list_of_jsons(r):
	out = {}
	keys = set(chain.from_iterable([list(rr.keys()) for rr in r]))
	keys_continue = []

	for key in keys:
		elements = []

		for rr in r:
			try:
				elements.append(rr[key])
			except:
				pass

		t = [isinstance(element, dict) for element in elements]

		if not any(t):
			elements = list(chain.from_iterable(elements)) if any([isinstance(element,list) for element in elements]) else elements

			try:
				out[key] = elements[0] if len(set(elements)) == 1 else elements
			except:
				out[key] = elements
		elif all(t):
			keys_continue.append(key)
			out[key] = elements
		else:
			raise NameError('Cannot merge jsons')

	#return defaultdict(lambda:'NA',out),keys_continue
	return out, keys_continue


def _merge_jsons(r):
	out = {}
	out,k1s = _join_list_of_jsons(r)

	for k1 in k1s:
		out[k1],k2s = _join_list_of_jsons(out[k1])
		for k2 in k2s:
			out[k1][k2],k3s = _join_list_of_jsons(out[k1][k2])
			for k3 in k3s:
				out[k1][k2][k3],k4s=_join_list_of_jsons(out[k1][k2][k3])
				for k4 in k4s:
					out[k1][k2][k3][k4],k5s=_join_list_of_jsons(out[k1][k2][k3][k4])
					for k5 in k5s:
						out[k1][k2][k3][k4][k5],k6s=_join_list_of_jsons(out[k1][k2][k3][k4][k5])
						for k6 in k6s:
							out[k1][k2][k3][k4][k5][k6],k7s=_join_list_of_jsons(out[k1][k2][k3][k4][k5][k6])
							for k7 in k7s:
								out[k1][k2][k3][k4][k5][k6][k7],k8s=_join_list_of_jsons(out[k1][k2][k3][k4][k5][k6][k7])
								if len(k8s):
									raise NameError('Depth exceeded')

	return out


def _chunker(seq, size):
	return (seq[pos:pos + size] for pos in range(0, len(seq), size))


def get_soup(title):
	"""
	Returns a BeautifulSoup object for the given title of the english Wikipedia page.
	"""
	r = requests.get('https://en.wikipedia.org/wiki/{}'.format(title))
	return BeautifulSoup(r.text, 'html.parser')


def wd_q(d, show=False):
	"""
	Queries the Wikidata API provided a dictionary of features.
	It handles the pages limit and the results limit by doing multiple queries and then merging the resulting json objects.

	Parameters
	----------
	d : dict
		Dictionary.
	show : boolean (False)
		If True it will print all the used urls.

	Returns
	-------
	r : dict
		Dictionary with the result of the query.

	Examples
	--------
	>>> r = j5.wp_q({'prop':'extracts','exintro':'','explaintext':'','pageids':736})
	>>> print(list(r['query']['pages'].values())[0]['extract'])
	"""
	base_url = 'https://www.wikidata.org/w/api.php?'

	d['action'] = 'wbgetentities' if 'action' not in set(d.keys()) else d['action']
	d['format'] = 'json'  if 'format' not in set(d.keys()) else d['format']

	use = 'ids'

	pages = d[use]
	pages = pages if _isiter(pages) else [pages]
	#pages = pages if hasattr(pages,'__iter__') else [pages]

	props = {}

	for u,v in d.items():
		if u != use:
			props[u] = str.join('|', [_string(vv) for vv in v]) if _isiter(v) else v
			#props[u] = '|'.join([_string(vv) for vv in v]) if hasattr(v,'__iter__') else v

	r = []

	for chunk in _chunker(pages,50):
		v = chunk
		p = {use:str.join('|', [_string(vv) for vv in v]) if _isiter(v) else v}
		#p = {use:'|'.join([_string(vv) for vv in v]) if hasattr(v,'__iter__') else v}
		url = base_url + urlencode(props) + '&' + urlencode(p)

		if show:
			print(url.replace(' ','_'))

		rr = _rget(url) #.json()
		r.append(rr)

	return _merge_jsons(r)


def wp_q(d,lang='en',continue_override=False,show=False):
	"""
	Queries the Wikipedia API provided a dictionary of features.
	It handles the pages limit and the results limit by doing multiple queries and then merging the resulting json objects.

	Parameters
	----------
	d : dict
		Dictionary.
	lang : str (default = 'en')
		Language edition to query.
	continue_override : boolean (False)
		If True it will not get any of the continuation queries.
	show : boolean (False)
		If True it will print all the used urls.

	Returns
	-------
	r : dict
		Dictionary with the result of the query.

	Examples
	--------
	>>> wp_q({'pageids':[306,207]})
	"""
	base_url = 'https://'+lang+'.wikipedia.org/w/api.php?'

	d['action'] = 'query' if 'action' not in set(d.keys()) else d['action']
	d['format'] = 'json'  if 'format' not in set(d.keys()) else d['format']

	if ('titles' in set(d.keys()))&('pageids' in set(d.keys())):
		raise NameError("Cannot use 'pageids' at the same time as 'titles'")

	use = 'pageids' if ('pageids' in set(d.keys())) else 'titles'
	pages = d[use]
	pages = pages if _isiter(pages) else [pages]
	#pages = pages if hasattr(pages,'__iter__') else [pages]
	#if use == 'titles':
	#	pages = [page.encode('utf-8') for page in pages if page is not None]  #IS ENCODING TO UTF-8

	props = {}

	for u,v in d.items():
		if u not in ['titles','pageids']:
			props[u] = str.join('|', [_string(vv) for vv in v]) if _isiter(v) else v
			#props[u] = '|'.join([_string(vv) for vv in v]) if hasattr(v,'__iter__') else v

	r = []

	for chunk in _chunker(pages,50):
		v = chunk
		p = {use:str.join('|', [_string(vv) for vv in v]) if _isiter(v) else v}

		for key,value in p.items():
			p[key] = value.encode('utf-8')

		url = base_url + urlencode(props) + '&' + urlencode(p)

		if show:
			print(url.replace(' ','_'))

		rr = _rget(url) #.json()

		while True:
			r.append(rr)

			if 'continue' in rr.keys() and not continue_override:
				continue_keys = [c for c in rr['continue'].keys() if c != 'continue']
				if len(continue_keys) > 1:
					print('Warning: more than one continue parameter found.')
					print(url.replace(' ','_'))

				continue_dict = {continue_keys[0] : rr['continue'][continue_keys[0]]}

				if show:
					print(url+'&'+urlencode(continue_dict)).replace(' ','_')

				rr = _rget(url+'&'+urlencode(continue_dict)) #.json()
			else:
				break

	return _merge_jsons(r)
