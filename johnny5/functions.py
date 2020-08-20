import re
import os, time, codecs, datetime as dt
from pandas import DataFrame
from itertools import chain

from urllib.request import *
from bs4 import BeautifulSoup

from .parse_functions import drop_comments
from .query import wd_q, wp_q, _rget


wiki_API = 'https://en.wikipedia.org/w/api.php?action=query&format=json'
wikidata_API = 'https://www.wikidata.org/w/api.php?action=wbgetentities&format=json'


def _dt2str(d):
	""" Transforms a datetime object into a string of the form yyyymmdd. """
	return str(d.year) + ('00'+str(d.month))[-2:] + ('00'+str(d.day))[-2:]


def _all_dates(d1, d2):
	""" Gets all the dates between the given dates. """
	delta = d2 - d1
	out = []
	for i in range(delta.days + 1):
		d = (d1 + dt.timedelta(days=i))
		out.append([int(d.year), int(d.month), int(d.day)])
	return DataFrame(out, columns=['year', 'month', 'day'])


def get_multiple_image(curid):
	""" Gets the first image that appears in the site (it is often the character's image).

	NEEDS TO BE UPDATED
	"""
	api_url = 'https://en.wikipedia.org/w/api.php?action=query&prop=revisions&rvprop=content&format=json&pageids='+str(curid)+'&rvsection=0'
	result = _rget(api_url)[u'query'][u'pages']
	r = result[unicode(curid)][u'revisions'][0][u'*']
	wikicode = mwparserfromhell.parse(r)
	templates = wikicode.filter_templates()
	box = {}
	for template in templates:
		name = template.name.lstrip().rstrip().lower()
		if 'image' in name:
			box_ = {}
			for param in template.params:
				key = drop_comments(param.name).strip().lower().replace(' ','_')
				value = drop_comments(param.value).strip()
				box_[key] = value
			box['image'] = box_
			break #Grab only the first one
	return box


def country(coords, path='', save=True, GAPI_KEY=None):
	'''
	WE NEED TO CHANGE THIS FUNCTION TO MAKE IT INDEPENDENT OF GAPI

	Uses the Google geocode API to get the country of a given geographical point.

	Parameters
	----------
	coords : (lat,lon) tuple
		Coordinates to query.
	path : string
		Path to save the json file containing the query result.
	save : boolean (True)
		If True it will save the result of the query as 'lat,lon.json'
	GAPI_KEY : string (None)
		Name of the environment variable holding the Google API key.

	Returns
	-------
	country : (name,code) tuple
		Country name and 2-digit country code.
	'''
	key = None
	if GAPI_KEY:
		key = os.environ.get(GAPI_KEY)

	latlng = '{},{}'.format(str(coords[0]), str(coords[1]))

	if key is not None:
		url = 'https://maps.googleapis.com/maps/api/geocode/json?latlng=' + latlng + '&project=Pantheon&key=' + key
	else:
		url = 'https://maps.googleapis.com/maps/api/geocode/json?latlng=' + latlng

	r = _rget(url) #.json()

	zero_results = False

	if r['status'] == 'OVER_QUERY_LIMIT':
		time.sleep(1)
		r = _rget(url) #.json()
	if r['status'] != 'OK':
		if r['status'] == 'OVER_QUERY_LIMIT':
			raise NameError('Query limit reached')
		elif r['status'] == 'ZERO_RESULTS':
			zero_results = True
		else:
			print(r)
			raise NameError('Unrecognized error')

	if save:
		f = open(path + latlng + '.json','w')
		json.dump(r, f)
		f.close()

	country = ('NULL', 'NULL')

	if not zero_results:
		for res in r['results']:
			for rr in res[u'address_components']:
				if 'country' in  rr['types']:
					country = (rr['long_name'], rr['short_name'])
				if country != ('NULL', 'NULL'):
					break
			if country != ('NULL', 'NULL'):
				break

	return country


def chunker(seq, size):
	"""
	Used to iterate a list by chunks.

	Parameters
	----------
	seq : list (or iterable)
		List or iterable to iterate over.
	size : int
		Size of each chunk

	Returns
	-------
	chunks : list
		List of lists (chunks)
	"""
	return (seq[pos:pos + size] for pos in range(0, len(seq), size))


def _dms2dd(lat):
    direc = lat[-1].lower()
    degs,mins,secs = (map(float,map(str,lat[:-1]))+[0.,0.])[:3]
    dd = degs+mins/60.+secs/(3600.)
    if (direc == 's')|(direc == 'w'):
        dd *=-1
    return dd


def wd_instances(cl, include_subclasses=False, return_subclasses=False):
	""" Gets all the instances of the given class.

	Parameters
	----------
	cl : str
		Wikidata code of the class
	include_subclasses : boolean (False)
		If True it will get all the instances in the given class and all its subclases.
	return_subclasses : boolean (False)
		If True not only it will get the inscances for all subclasses, but will return the set of subclasses.

	Returns
	-------
	instances : set
		wd_id for every instance of the given class.
	subclasses : set
		wd_id for every subclass for cl, and their subclasses
		(only when return_subclasses if True)

	Examples
	--------
	To get all universities:
	>>> wd_instances('Q3918')
	To get all humans:
	>>> wd_instances('Q5', include_subclasses=False)
	"""
	if include_subclasses:
		queried = set([])
		to_query = set([cl])
		print("Retrieving subclasses.")
	else:
		queried = set([cl])
		to_query = set([])

	while len(to_query) != 0:
		query = _wd_subclasses(to_query)
		queried.update(to_query)
		to_query = query.difference(queried)

	if include_subclasses:
		print("Found a total of {} subclasses.".format(str(len(queried))))

	print("Retrieving instances.")
	instances = _wd_instances(queried)

	if return_subclasses and include_subclasses:
		return instances, queried
	else:
		return instances


def wd_subclasses(cl, include_subclasses=False):
	"""
	Gets all the subclasses of the given class.

	Parameters
	----------
	cl : str
		Wikidata code of the class
	include_subclasses : boolean (False)
		If True it will get all the subclasses of the given class and all its subclases.

	Returns
	-------
	subclasses : set
		wd_id for every subclass of the given class.

	Examples
	--------
	To get all subclasses of musical ensemble:
	>>> wd_subclasses('Q2088357', include_subclasses=True)
	"""
	if include_subclasses:
		queried = set([])
		toquery = set([cl])

		while len(toquery) != 0:
			for c in toquery:
				query = _wd_subclasses(c)
				toquery.discard(c)
				queried.add(c)
				toquery = toquery|query.difference(queried)
				break
	else:
		queried = _wd_subclasses(cl)

	queried.discard(cl)
	return queried


def _wd_clear():
	""" Deletes the temp files with the subclasses and classes. """
	path = _dumps_path()
	path_os = _path(path)
	files = os.listdir(path)

	instances = os.listdir(path + 'instances/')
	subclasses = os.listdir(path + 'subclasses/')

	for c in instances:
		if '_temp' in c:
			os.system("rm {}instances/{}".format(path_os, cl))

	for c in subclasses:
		if '_temp' in c:
			os.system("rm {}subclasses/{}".format(path_os, cl))


def _wd_instances(cl_ids):
	""" Gets all the instances of the given class, without worrying about subclasses. """
	cl_ids = list(cl_ids)
	pattern = r".*<[^>]*P31>.*<[^>]*(" + '|'.join(cl_ids) + r")> \."

	path = _dumps_path()
	path_os = _path(path)
	files = os.listdir(path)

	os.system('rm {}/instances/*'.format(path_os))

	filename = [f for f in files if 'latest-all' in f]

	F = open("{}instances/people.nt".format(path), mode='w')

	if len(filename) == 0:
		raise NameError('No dump found, please run:\n\t>>> download_latest()')
	else:
		filename = filename[0]

	print('Parsing the dump {}'.format(filename))

	with open('{}{}'.format(path_os, filename)) as f:
		for line in f:
			m = re.match(pattern, line)
			if m:
				F.write(line)

	F.close()

	lines = open("{}instances/people.nt".format(path)).read().split('\n')
	instances = set([line.split(' ')[0].split('/')[-1].split('>')[0].split('S')[0].split('-')[0] for line in lines if line != ''])

	return instances


def _wd_subclasses(cl_ids):
	""" Gets all the subclasses of the given class. """
	cl_ids = list(cl_ids)
	pattern = r".*<[^>]*P279>.*<[^>]*(" + '|'.join(cl_ids) + r")> \."

	path = _dumps_path()
	path_os = _path(path)
	files = os.listdir(path)

	os.system('rm {}/subclasses/*'.format(path_os))

	filename = [f for f in files if 'latest-all' in f]

	F = dict()
	for id_ in cl_ids:
		F[id_] = open("{}subclasses/{}.nt".format(path, id_), mode='w')

	if len(filename) == 0:
		raise NameError('No dump found, please run:\n\t>>> download_latest()')
	else:
		filename = filename[0]

	print('Parsing the dump {}'.format(filename))

	with open('{}{}'.format(path_os, filename)) as f:
		for line in f:
			m = re.match(pattern, line)
			if m:
				id_ = m.group(1)
				F[id_].write(line)

	for id_ in cl_ids:
		F[id_].close()

	subclasses = set()

	for id_ in cl_ids:
		lines = open(path + 'subclasses/' + id_ + ".nt").read().split('\n')
		subclasses.update(set([line.split(' ')[0].split('/')[-1].split('>')[0].split('S')[0].split('-')[0] for line in lines if line != '']))

	return subclasses


def all_wikipages(update=False):
	'''Downloads all the names of the Wikipedia articles'''
	path = _dumps_path()
	files = os.listdir(path)

	if 'enwiki-allarticles.txt' not in files or update:
		if 'enwiki-latest-abstract.xml' not in files or update:
			print('Downloading dump')
			urlretrieve(
				'https://dumps.wikimedia.org/enwiki/latest/enwiki-latest-abstract.xml.gz',
				'{}enwiki-latest-abstract.xml.gz'.format(path)
			)
			os.system('gunzip {}enwiki-latest-abstract.xml.gz'.format(path))
		if 'enwiki-latest-titles.xml' not in files or update:
			print('Parsing titles from dump')
			os.system("grep '<title>'  {}enwiki-latest-abstract.xml > {}enwiki-latest-titles.xml".format(
				_path(path), _path(path)
			))

		print('Cleaning titles')

		f = codecs.open('{}enwiki-latest-titles.xml'.format(path), encoding='utf-8')
		g = open('{}enwiki-allarticles.txt'.format(path), mode='w')

		while True:
			line = f.readline()
			line = line[17:-9].strip()
			g.write((line+'\n'))
			if not line:
				break

		f.close()
		g.close()

		print('Cleaning up')

		os.remove('{}enwiki-latest-titles.xml'.format(path))

	titles = set(codecs.open('{}enwiki-allarticles.txt'.format(path), encoding='utf-8').read().split('\n'))
	titles.discard('')

	return titles


def _dumps_path():
	""" Returns the path where the dumps are stored.
	Note that the path can be set in the first line of a dumps.txt file.
	"""
	path = os.path.split(__file__)[0] + '/data/'
	files = os.listdir(path)

	if 'dumps.txt' in files:
		path = open(path + 'dumps.txt').read().split('\n')[0]

	return path


def _set_new_dumps_path(new_path):
	""" Modifies the dump """
	old_path  = _dumps_path()
	data_path = os.path.split(__file__)[0]+'/data/'

	if new_path=='default':
		new_path = data_path
	else:
		new_path = os.path.abspath(new_path)+'/'

	if old_path!=new_path:
		if os.path.exists(new_path):
			_move_dumps(old_path,new_path)

			if new_path==data_path:
				os.remove(data_path+'dumps.txt')
			else:
				f = open(data_path+'dumps.txt',mode='w')
				f.write(new_path)
				f.close()

			print('Dumps path changed from:\n'+old_path+'\nto:\n'+new_path)
		else:
			raise NameError('Directory not found:\n'+new_path)
	else:
		print('Dumps path not changed.')


def dumps_path(new_path=None):
	"""
	Handle the path to the Wikipedia and Wikidata dumps.
	If new_path is provided, it will set the new path.

	Parameters
	----------
	new_path : str (optional)
		If provided it will set the dumps path to this path.
		Path where to store the Wikipedia and Wikidata dumps.
		(Must be full not relative path)
		To reset the default path pass new_path='default'

	Returns
	-------
	path : str
		Current path to dumps
	"""
	if new_path is not None:
		_set_new_dumps_path(new_path)
		return _dumps_path()


def _move_dumps(old_path,new_path):
	""" Moves Wikipedia and Wikidata dumps to a new location. """
	wikipedia_dump = _dump_filename('wp')
	wikidata_dump  = _dump_filename('wd')

	if wikipedia_dump in os.listdir(old_path):
		os.rename(old_path+wikipedia_dump, new_path+wikipedia_dump)
	if (wikidata_dump in os.listdir(old_path))&(wikidata_dump is not None):
		os.rename(old_path+wikidata_dump,  new_path+wikidata_dump)


def _dump_filename(wiki):
	""" Gets the name of the filename of the given wiki """
	path = _dumps_path()

	if wiki == 'wd':
		files = os.listdir(path)
		filename = [f for f in files if 'latest-all' in f]

		print(len(filename))
		print(filename)

		if len(filename) == 1:
			filename=filename[0]
			return filename
		elif len(filename)>1:
			pass
			# Handle multiple wikidata dumps
		else:
			#Handle missing wikidata dump
			pass
	elif wiki == 'wp':
		return 'enwiki-latest-abstract.xml'
	else:
		raise NameError('Unknown Wiki referenced')


def latest_wddump():
	""" Gets the name latest Wikidata RDF dump. """
	# url = 'http://tools.wmflabs.org/wikidata-exports/rdf/exports.html'
	# url = 'https://dumps.wikimedia.org/other/wikidata/'
	url = 'https://dumps.wikimedia.org/wikidatawiki/entities/'

	conn = urlopen(url)
	html = conn.read()
	soup = BeautifulSoup(html, "html.parser")

	for line in str(soup.find('pre')).split('\n'):
		link = BeautifulSoup(line, "html.parser").find('a').get('href',None)
		if link == 'latest-all.nt.gz':
			for d in line.split(' '):
				if d!='':
					try:
						link_date = dt.datetime.strptime(d,'%d-%b-%Y')
						break
					except:
						pass
			break

	latest_dump_date = link_date
	latest_dump_url  = url + link

	return latest_dump_url, latest_dump_date


def check_wpdump():
	""" Used to check the current status of the Wikipedia Dump.
	It returns None, but prints the information.
	"""
	path = _dumps_path()
	dt = time.ctime(os.path.getmtime(path + 'enwiki-latest-abstract.xml'))
	print('Dump downloaded on:')
	print('\t{} {} {}'.format(
			dt.split(' ')[1],
			dt.split(' ')[3],
			dt.split(' ')[-1]
		))
	print('To update run:\n\t>>> all_wikipages(update=True)')


def check_wddump():
	""" Used to check whether the Wikidata dump found on file is up to date.

	Returns
	-------
	status : boolean
		True if it is necessary to update
	"""
	url, top_date = latest_wddump()
	path = _dumps_path()
	files = os.listdir(path)
	filename = [f for f in files if 'latest-all' in f]

	if len(filename) == 0:
		# No dump found
		return True
	else:
		filename = filename[0]

	if filename.split('_')[-1].split('.')[0] == str(top_date).split(' ')[0]:
		# Dump is ip to date
		return False
	else:
		# Dump is outdated
		return True


def _path(path):
	path_os = path[:]
	for c in [' ', '(', ')']:
		path_os = path_os.replace(c, '\\'+c)
	return path_os


def download_latest():
	""" Downloads the latest Wikidata RDF dump.

	If the dump is updated, it will delete all the instances files.
	"""
	url, top_date = latest_wddump()
	filename = url.split('/')[-1].split('.')[0]+'_'+str(top_date).split(' ')[0]+'.nt.gz'
	path = _dumps_path()

	drop_instances = False

	if filename.replace('.gz', '') not in set(os.listdir(path)) and filename not in set(os.listdir(path)):
		print("Downloading file from: {}".format(url))
		print("Saving file into {}".format(path + filename))
		urlretrieve(url, '{}{}'.format(path, filename))
	else:
		print("No update needed.")

	if filename.replace('.gz', '') not in set(os.listdir(path)) and filename in set(os.listdir(path)):
		print("Unzipping file")
		path_os = _path(path)
		print('gunzip {}{}'.format(path_os, filename))
		os.system('gunzip {}{}'.format(path_os, filename))
		drop_instances = True

	remove = [f for f in os.listdir(path) if 'latest-all' in f and f != filename.replace('.gz','') and f != filename]

	if len(remove) != 0 and drop_instances:
		print('Cleaning up')

		for f in remove:
			os.remove(path + f)

	if drop_instances:
		# NOTE: Don't think this is needed anymore since the gunzip command above should
		# remove this file upon completion.
		# os.remove(path + filename)
		remove = os.listdir(path + 'instances/')

		for f in remove:
			print('Remove ', path + 'instances/' + f)
			os.remove(path + 'instances/' + f)

		remove = os.listdir(path + 'subclasses/')

		for f in remove:
			print('Remove ', path + 'subclasses/' + f)
			os.remove(path + 'subclasses/' + f)
